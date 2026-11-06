(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__LibAtomic () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibAtomic."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibAtomic.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2eq"; "3Z"; "4Segment"; "5MachineOk"; "5fetch_word"; "5is_ecall"; "5machine_result"]; ["5machine_state"; "5ms_svc_pending"; "5step"; "6decode_any"; "7BC_EQ"; "7BC_NE"; "7Branch"; "7branch_cond"; "7instr"; "8bvmap"; "9branch_taken"; ";mkst_r"; ":mkst_r"; "<btgt"; "<c_eq"; "<getr"]; ["<v_addi"; "0c"; "0fx"; "0imm"; "0mem"; "0pc"; "0r"; "0regs"; "0rom"; "0rs1"; "0rs2"; "0segs"; "=bv"; "=bv_signed"; "0w"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : word)
: machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := Some r; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Lemma mkst_r_svc : ltac2:(TCodec.tc2 tcn__LibAtomic "N&Iy5'Q<yR0%211%5241'5y8%611%311p061'9%618&A&Kr5r4r3r2r1%6554321%811(0%11C%=3<31pR>E1pRB@1pR:A1pR<H1pR@H1").
Proof. reflexivity. Qed.
End FPX_1.
Ltac atomic_pipeline Hfetch Hecall Hdecode :=
unfold mkst_r;
step_pipeline Hfetch Hecall Hdecode;
cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
rewrite ?bv_eqb0_is_x0.
Ltac norm_pc_r :=
try lazymatch goal with
| |- CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
end.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma step_lr_w : forall segs regs pc mem rom w aq rl rd rs bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr AW aq rl rd rs, 4%Z) ->
(bv_unsigned (getr regs rs) mod 4 = 0)%Z ->
rdn segs mem (getr regs rs) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
(v_addi pc 4) mem rom (getr regs rs)).
Proof.
intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite ov_rdn, Hread. cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma step_lr_d : forall segs regs pc mem rom w aq rl rd rs bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr AD aq rl rd rs, 4%Z) ->
(bv_unsigned (getr regs rs) mod 8 = 0)%Z ->
rdn segs mem (getr regs rs) 8%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom (getr regs rs)).
Proof.
intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite ov_rdn, Hread. cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
r = getr regs rs1 ->
RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
(wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
subst r. rewrite Z.eqb_refl. cbv beta iota.
rewrite Hok. cbv beta iota.
rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
r = getr regs rs1 ->
RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
(wbytes mem (getr regs rs1) (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
subst r. rewrite Z.eqb_refl. cbv beta iota.
rewrite Hok. cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4.
unfold regupd, word_to_le_bytes.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma step_sc_fail : forall segs regs pc mem rom w wd aq rl rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
unfold amo_bytes in Hal. rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite b_npc4. unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma step_sc_mismatch : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
(bv_unsigned r =? bv_unsigned (getr regs rs1))%Z = false ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hne.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
unfold amo_bytes in Hal. rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite Hne. cbv beta iota.
rewrite b_npc4. unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
Lemma step_branch_tk_r : ltac2:(TCodec.tc2 tcn__LibAtomic "S0'4';%211&Iy5'Q<yR0%211%5241'5y8%611%311p061yQ0%:11'G%<1=y=%>11'9%<16&=r;r9%3221(1r5%22=1%93841'2&>r6%211(3%?3521'7'H':%3221%O11&Cr7%211(6(Fr4r3%34@E21+4%64=<21%I2<1%Q03<91&J&Or=%221H%322N%53@21(8%Q83N21'?'@%211&Br?&LvQ2r>r<r:%5643@2Q@1%8271(<&M&Q=%12QJQA%32F1%<6;:19QG8%62A1%QL3A81p0E1p0N1p0Q@1p0QG1pR8R21pRFR51pRDR61pR4R81pRNR:1pR>RC1pRBR>1pR:R?1pR<RF1pR@RF1pRHRM1").
Proof.
intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.
Lemma step_branch_ft_r : ltac2:(TCodec.tc2 tcn__LibAtomic "RM'4';%211&Iy5'Q<yR0%211%5241'5y8%611%311p061yQ0%:11'G%<1=y=%>11'9%<16&=r;r9%3221(1r5%22=1%93841'2&>r6%211(3%?3521'7'H':%3221%O11&Cr7%211(6(Fr4r3%34@E21+4%64=<21%I2<1%Q03<91&J&Or=%221H%322N%53@21%Q73M1I'?'@%211&Br?&LvQ2r>r<r:%5643?2Q?1%8271(<&Q0%12CI%:69817QD6%42?1%QI3?61p0C1p0K1p0Q=1p0QD1pR8QO1pRFR21pRDR31pR4R51pRNR71pR>R@1pRBR;1pR:R<1pR<RC1pR@RC1pRHRJ1").
Proof.
intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.
Lemma step_bne_tk_r : ltac2:(TCodec.tc2 tcn__LibAtomic "RM'4';%211&Iy5'Q<yR0%211%5241'5y8%611%311p061yQ0%:11%;1<y=%=11'9%;15&=r:r8%3221(1r4%22<1%93841'2&>r5%211(3%?3521'7'H':%3221%N11&Cr6%211(6(F(Er3%342@E1+4%64=<21%I2<1%Q03<91&N&Or<%221>%322I%5221%Q73M1I'?'@%211&Br>&LvQ2r=r;r9%5643?2Q?1%8271(<&M&Q=%12QIQ;%32E1%<6;:19QF8%62A1%QK3A81p0E1p0M1p0Q?1p0QF1pR8R11pRFR41pRDR51pRNR71pR>R@1pRBR;1pR:R<1pR<RC1pR@RC1pRHRJ1").
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_bne_ft_r : ltac2:(TCodec.tc2 tcn__LibAtomic "RL'4';%211&Iy5'Q<yR0%211%5241'5y8%611%311p061yQ0%:11%;1<y=%=11'9%;15&=r:r8%3221(1r4%22<1%93841'2&>r5%211(3%?3521'7'H':%3221%N11&Cr6%211(6(F(Er3%342@E1+4%64=<21%I2<1%Q03<91&N&Or<%221>%322I%5221(8%Q83N21'?'@%211&Br>&LvQ2r=r;r9%5643@2Q@1%8271(<&Q0%12DJ%:69817QE6%42?1%QJ3?61p0C1p0L1p0Q>1p0QE1pR8R01pRFR31pRDR41pRNR61pR>R?1pRBR:1pR:R;1pR<RB1pR@RB1pRHRI1").
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_beq_tk_r : ltac2:(TCodec.tc2 tcn__LibAtomic "RN'4';%211&Iy5'Q<yR0%211%5241'5y8%611%311p061yQ0%:11%;1<y=%=11'9%;15&=r:r8%3221(1r4%22<1%93841'2&>r5%211(3%?3521'7'H':%3221%N11&Cr6%211(6(F(Dr3%342@E1+4%64=<21%I2<1%Q03<91&N&Or<%221>%322I%5221(8%Q83N21'?'@%211&Br>&LvQ2r=r;r9%5643@2Q@1%8271(<&M&Q=%12QJQ<%32F1%<6;:19QG8%62A1%QL3A81p0E1p0N1p0Q@1p0QG1pR8R21pRFR51pRDR61pRNR81pR>RA1pRBR<1pR:R=1pR<RD1pR@RD1pRHRK1").
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.
Lemma step_beq_ft_r : ltac2:(TCodec.tc2 tcn__LibAtomic "RK'4';%211&Iy5'Q<yR0%211%5241'5y8%611%311p061yQ0%:11%;1<y=%=11'9%;15&=r:r8%3221(1r4%22<1%93841'2&>r5%211(3%?3521'7'H':%3221%N11&Cr6%211(6(F(Dr3%342@E1+4%64=<21%I2<1%Q03<91&N&Or<%221>%322I%5221%Q73M1I'?'@%211&Br>&LvQ2r=r;r9%5643?2Q?1%8271(<&Q0%12CI%:69817QD6%42?1%QI3?61p0C1p0K1p0Q=1p0QD1pR8QO1pRFR21pRDR31pRNR51pR>R>1pRBR91pR:R:1pR<RA1pR@RA1pRHRH1").
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.
Lemma step_opimm_r : forall segs regs pc mem rom r w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w op rd rs imm Hfetch Hecall Hdecode.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_op_r : forall segs regs pc mem rom r w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w op rd rs1 rs2 Hfetch Hecall Hdecode.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
End FPX_2.
