(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "True"; "or"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_add"; "bv_signed"; "bv_concat"; "bv_unsigned"; "bv_and"; "bv_not"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "aluop"; "Ecall"; "branch_cond"; "mulop"; "ALU_ADD"; "Auipc"; "Branch"; "Fence"; "FenceI"; "Jal"; "Jalr"; "Lui"; "Mul"; "Mul32"; "Op"; "Op32"; "OpImm"; "OpImm32"; "ShiftImm"; "ShiftImm32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_pc"; "smatch"; "valuation"; "sstate"; "sv"; "SLit"; "eval"; "ss_facts"; "ss_next"; "holds"; "sprop"; "SPBranch"; "SPNot"; "agree_below"; "sprop_below"; "sv_below"; "swf"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "MachineOk"; "machine_result"; "step"; "ms_mem"; "ms_pc"; "ms_pc_val"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Corelib.Init.Datatypes"; "list"; "pair"; "Some"; "option"; "bool"; "true"; "prod"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_pc"; "instr_at"; "get_reg"; "set_reg"; "decision"; "immI"; "add_fact"; "mk_slt_f"; "decide_branch"; "mk_aluw_f"; "lit_of"; "mk_addk"; "mk_aluw"; "mk_md_f"; "mk_mdw_f"; "same_base_eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.S2"; "next_rel"; "@Stdlib.ZArith.BinInt.Z"; "add"; "modulo"; "pow"; "land"; "lnot"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA"; "core_of"; "ms_of"; "@LinuxProcessSemantics.Riscv.Sem"; "with_pc"; "EDone"; "branch_taken"; "eff"; "exec"; "low32"; "rget"; "rset"; "w1"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "bv_eqb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "Forall"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S2.
Variable segs : list Segment.

Lemma rget_match : ltac2:(tb__ "0|1|
S25S26S3dS45A1M0S34S46S6Q5A1S24Vsegs;R6R5S3eG0S3bR4S3cR3R2A2A4A4S0S6Q40A1S68S60R4A1R2A2S29R7S49R6R2A2A2A3F_;Fr;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md r Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & _).
  cbn [fst snd cfg_ms cfg_model] in Hregs.
  unfold rget, core_of, get_reg, reg_sv. cbn [c_regs]. rewrite is_x0_regZ. unfold regZ.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [E|E].
  - reflexivity.
  - unfold regs_match in Hregs. rewrite (Hregs r E). unfold reg_sv.
    destruct (Z.eqb_spec (bv_unsigned r) 0); [lia|reflexivity].
Qed.

Lemma smatch_pc_only : ltac2:(tb__ "0|1|
S25S26S3dS45A1M0S34S46S5eS24Vsegs;R6R5S3eG0S3bR4S3cR3R2A2A4A4S24Vsegs;R7S47R6R2A2S3eG0S3bR5S3cS61R4S62S7Q40R2A2S60R4A1A2S38R4A1A3R3A2A4A4F_;Fpc';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md pc' Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch; cbn [fst snd cfg_ms cfg_model].
  unfold ms_of, with_pc, core_of; cbn [c_regs c_fregs c_pc c_fcsr c_resv].
  split; [exact Hwf|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|]. split; [exact Hregs|]. split; [exact Hfregs|].
  split; [exact Hfcsr|]. split; [exact Hresv|]. split; [|exact Hfacts].
  apply (mem_match_same_mem segs rho (ss_objs S) ms); [reflexivity|reflexivity|exact Hmem].
Qed.

Lemma smatch_add_fact : ltac2:(tb__ "0|0|
S25S26S43S3dS45A1S3bA2S2dS24Vsegs;R4R3R2A4S0S41S31S2bR4A1R2A2S42A3S2cR6R3A2S24Vsegs;R7S4dR6R4A2R5A4F_;F_;F_;Fp;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] p Hsm Hb Hp.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch; cbn [fst snd cfg_ms cfg_model add_fact ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts] in *.
  split; [apply swf_add_fact; assumption|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|]. split; [exact Hregs|]. split; [exact Hfregs|].
  split; [exact Hfcsr|]. split; [exact Hresv|]. split; [exact Hmem|].
  constructor; assumption.
Qed.

Lemma smatch_swf : ltac2:(tb__ "0|0|
S25S26S43S3dS45A1S3bA2S24Vsegs;R3R2R1A4S0S41S33R3A1S42A3F_;Fw;FS;Frho;").
Proof using . intros rho S w H. exact (proj1 H). Qed.

Lemma smatch_pcv : ltac2:(tb__ "0|2|
S25S26S3dS45A1M0S34S46S24Vsegs;R5R4S3eG0S3bR3S3cR2R1A2A4A4S0S6Q40M1A1S39R3A1S7G1S23R5A1A2A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. exact (proj1 (proj2 H)). Qed.

Lemma smatch_facts : ltac2:(tb__ "0|0|
S25S26S43S3dS45A1S3bA2S24Vsegs;R3R2R1A4S6eS2dS2cR4A1S2aR3A1A3F_;Fw;FS;Frho;").
Proof using . intros rho S w H. unfold smatch in H. tauto. Qed.

Lemma pc_plus : ltac2:(tb__ "0|1|
S5eS5eS0S6Q40M0A1S8G0S7G0R2A2S7G0R1A2A3S7G0S59S58R2R1A2S5aZ2Z40A2A2A2A3Fk;Fpc;").
Proof using . intros. rewrite bv_add_ZZ, Z_to_bv64_mod. reflexivity. Qed.

Lemma pc_plus' : ltac2:(tb__ "0|1|
S5eS5eS0S6Q40M0A1S8G0S7G0R2A2S7G0R1A2A3S7G0S58R2R1A2A2A3Fk;Fpc;").
Proof using . intros. rewrite bv_add_ZZ. reflexivity. Qed.

Definition next_rel (S S' : sstate) (rho : valuation) (tr : list event) (ms : machine_state) (md : Model) : Prop := ltac2:(tb__ "0|1|
S2S34S34S2S25S25S1S0S36S34A1S37Vsegs;Vms;A2S35S34R2A2A3S1S30S2bVS;A1M0Vrho;R1A3S1S6dG0S2bVS';A1A2S24Vsegs;R1VS';S3eS3dS45A1S3bVtr;S3cR2Vmd;A2A4A4A2A2A2Lrho';A2Lms';A2").

Lemma next_rel_same_rho : ltac2:(tb__ "0|1|
S26S26S25S3dS45A1M0S34S46S34S0S36S34A1S37Vsegs;R3A2S35S34R1A2A3S6dS2bR8A1S2bR7A1A2S24Vsegs;R7R8S3eG0S3bR6S3cR3R4A2A4A4S57RaR9R8R7R6R5A6F_;F_;F_;Fms';Fmd;Fms;Ftr;Frho;FS';FS;").
Proof using .
  intros. exists ms', rho. split; [assumption|]. split; [apply agree_below_refl|]. split; assumption.
Qed.

Lemma ss_next_set_pc_reg : ltac2:(tb__ "0|0|
S26S6Q5A1S27S5eS0S5fS2bS47S4aR4R3R2A3R1A2A1S2bR4A1A3Fpc;Fe;Frd;FS;").
Proof using . intros. cbn. apply ss_next_set_reg. Qed.

Lemma step_rd_sound : ltac2:(tb__ "0|4|
S25S26S3dS45A1M0S34S46SeS6Q5A1S6Q40M1A1M2S27G2S5eS24Vsegs;RbRaS3eG0S3bR9S3cR8R7A2A4A4S0S40SeA1S48Vsegs;S23RbA1A2S3fSeR7A2A3S3S0SeR8S10A3A1S0S65S66S7G1Z4A2R9S60RbA1M3A3S63S69R8R7S62R5G3A2A3A1A3S0G2R6S7G1R5A2A3S0S41S32S2bRfA1R8A2S42A3S0G2S29R11R9A2RaA3S57R11S47S4aR11RcRaA3R8A2R12R10RfReA6F_;F_;F_;F_;F_;F_;F_;Fpc';Fp;Fe;Fv;Frd;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i rd v e p pc' Hsm Hi Hne Hex Hp He Hev.
  pose proof (smatch_pcv _ _ _ _ _ Hsm) as Hpc.
  eapply next_rel_same_rho.
  - rewrite (step_instr_at segs ms (ss_pc S) i Hpc Hi Hne). rewrite Hex. cbn [interp_eff0 lift_result].
    reflexivity.
  - rewrite ss_next_set_pc_reg. lia.
  - rewrite Hp. eapply smatch_rd_pc; eauto.
Qed.

Lemma step_pc_sound : ltac2:(tb__ "0|4|
S25S26S3dS45A1M0S34S46SeS6Q40M1A1M2S5eS24Vsegs;R8R7S3eG0S3bR6S3cR5R4A2A4A4S0S40SeA1S48Vsegs;S23R8A1A2S3fSeR4A2A3S3S0SeR5S10A3A1S0S65S66S7G1Z4A2R6S60R8A1M3A3S63S62R5G3A2A1A3S0G2R6S7G1R5A2A3S57RcS47RcR6A2RdRbRaR9A6F_;F_;F_;F_;F_;Fpc';Fp;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i p pc' Hsm Hi Hne Hex Hp.
  pose proof (smatch_pcv _ _ _ _ _ Hsm) as Hpc.
  eapply next_rel_same_rho.
  - rewrite (step_instr_at segs ms (ss_pc S) i Hpc Hi Hne). rewrite Hex. cbn [interp_eff0 lift_result].
    reflexivity.
  - cbn. lia.
  - rewrite Hp. eapply smatch_pc_only; eauto.
Qed.

Lemma npc_eq : ltac2:(tb__ "0|3|
S25S26S3dS45A1M0S34S46S24Vsegs;R5R4S3eG0S3bR3S3cR2R1A2A4A4S0S6Q40M1A1S8G1S3aR3A1S7G1Z4M2A2A3S7G1S58S23R5A1G2A2A2A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros. pose proof (smatch_pcv _ _ _ _ _ H) as Hpc. unfold ms_pc in Hpc. rewrite Hpc. apply pc_plus'.
Qed.

Ltac below_tac :=
  repeat first [ reflexivity
               | apply mk_slt_f_below | apply mk_aluw_f_below | apply mk_ext_f_below
               | apply mk_alu_f_below | apply mk_alu_below | apply mk_aluw_below | apply mk_md_f_below | apply mk_mdw_f_below | apply mk_md_below | apply mk_mdw_below
               | apply mk_ext_below | apply mk_addk_below
               | apply get_reg_below | apply get_freg_below
               | eapply smatch_swf; eassumption ].

Lemma case_opimm : ltac2:(tb__ "0|2|
S26SfS6Q5A1M0G0S6QcA1S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS1fR8R7R6R5A4A2A3S24Vsegs;R5RaS3eG1S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S4eS2aRbA1RaS49RbR8A2S28S59S4cR7A1S5aZ2Z40A2A2A1A4A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fimm;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_slt_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- (rget_match rho S tr ms md rs1 Hsm).
  cbn [eval]. rewrite Z_to_bv64_mod. reflexivity.
Qed.

Lemma case_shiftimm : ltac2:(tb__ "0|3|
S26SfS6Q5A1M0G0S6Q6M1A1S25S3dS45A1M2S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS21R8R7R6R5A4A2A3S24Vsegs;R5RaS3eG2S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S4eS2aRbA1RaS49RbR8A2S28SbG1R7A2A1A4A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fsh;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_slt_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- (rget_match rho S tr ms md rs1 Hsm). reflexivity.
Qed.

Lemma case_op : ltac2:(tb__ "0|2|
S26SfS6Q5A1M0G0G0S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS1dR8R7R6R5A4A2A3S24Vsegs;R5RaS3eG1S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S4eS2aRbA1RaS49RbR8A2S49RbR7A2A4A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_slt_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- !(rget_match rho S tr ms md _ Hsm). reflexivity.
Qed.

Lemma low32_lit : ltac2:(tb__ "0|1|
S5eS0S6Q20M0A1S67S7Q40R1A2A1S7G0R1A2A3Fz;").
Proof using .
  intros z. unfold low32. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite two64.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia |].
  exists (2 ^ 32). reflexivity.
Qed.

Lemma low32_lit_mod : ltac2:(tb__ "0|1|
S5eS0S6Q20M0A1S67S7Q40S59R1S5aZ2Z40A2A2A2A1S7G0R1A2A3Fz;").
Proof using . intros. rewrite Z_to_bv64_mod. apply low32_lit. Qed.

Lemma case_opimm32 : ltac2:(tb__ "0|2|
S26S6Q5A1M0G0S6QcA1S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R8A1A2S3fSeS20R7R6R5A3A2A3S24Vsegs;R5R9S3eG1S3bR4S3cR3R2A2A4A4S57RaS47S4aRaR9S50S2aRaA1S13S49RaR8A2S28S59S4cR7A1S5aZ2Z40A2A2A1A4A3S58S23RaA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fimm;Frs1;Frd;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_aluw_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- (rget_match rho S tr ms md rs1 Hsm). cbn [eval].
  rewrite low32_lit_mod. reflexivity.
Qed.

Lemma case_shiftimm32 : ltac2:(tb__ "0|3|
S26SfS6Q5M0A1M1G1G1S25S3dS45A1M2S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS22R8R7R6R5A4A2A3S24Vsegs;R5RaS3eG2S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S53RaS49RbR8A2S28SbG0R7A2A1A3A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fsh;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite mk_aluw_sound. rewrite <- (rget_match rho S tr ms md rs1 Hsm). cbn [eval].
  rewrite low32_lit. reflexivity.
Qed.

Lemma case_op32 : ltac2:(tb__ "0|2|
S26SfS6Q5A1M0G0G0S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS1eR8R7R6R5A4A2A3S24Vsegs;R5RaS3eG1S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S50S2aRbA1RaS49RbR8A2S49RbR7A2A4A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_aluw_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- !(rget_match rho S tr ms md _ Hsm). reflexivity.
Qed.

Lemma case_mul : ltac2:(tb__ "0|2|
S26S12S6Q5A1M0G0G0S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS1bR8R7R6R5A4A2A3S24Vsegs;R5RaS3eG1S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S54S2aRbA1RaS49RbR8A2S49RbR7A2A4A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_md_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- !(rget_match rho S tr ms md _ Hsm). reflexivity.
Qed.

Lemma case_mul32 : ltac2:(tb__ "0|2|
S26S12S6Q5A1M0G0G0S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS1cR8R7R6R5A4A2A3S24Vsegs;R5RaS3eG1S3bR4S3cR3R2A2A4A4S57RbS47S4aRbR9S55S2aRbA1RaS49RbR8A2S49RbR7A2A4A3S58S23RbA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | below_tac |].
  rewrite (mk_mdw_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- !(rget_match rho S tr ms md _ Hsm). reflexivity.
Qed.

Lemma case_lui : ltac2:(tb__ "0|4|
S26S6Q5A1S6Q14M0A1S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R7A1A2S3fSeS1aR6R5A2A2A3S24Vsegs;R5R8S3eG1S3bR4S3cR3R2A2A4A4S57R9S47S4aR9R8S51S6bQ20M2Q40SaG2G0QcM3R7S7G3Z0A2A5A3A1A3S58S23R9A1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fimm;Frd;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | reflexivity |].
  apply lit_of_sound.
Qed.

Lemma case_auipc : ltac2:(tb__ "0|5|
S26S6Q5A1S6Q14M0A1S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R7A1A2S3fSeS14R6R5A2A2A3S24Vsegs;R5R8S3eG1S3bR4S3cR3R2A2A4A4S57R9S47S4aR9R8S28S59S58S23R9A1M2S9Q20M3SaG3G0QcM4R7S7G4Z0A2A5A2A2S5aZ2Z40A2A2A1A3S58G2Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fimm;Frd;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | reflexivity |].
  cbn [eval]. rewrite Z_to_bv64_mod.
  pose proof (smatch_pcv _ _ _ _ _ Hsm) as Hpc. unfold ms_pc in Hpc.
  unfold core_of; cbn [c_pc]. rewrite Hpc. rewrite <- pc_plus'. reflexivity.
Qed.

Lemma case_jal : ltac2:(tb__ "0|4|
S26S6Q5A1S6Q15M0A1S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R7A1A2S3fSeS18R6R5A2A2A3S24Vsegs;R5R8S3eG1S3bR4S3cR3R2A2A4A4S57R9S47S4aR9R8S28S59S58S23R9A1M2Z4A2S5aZ2Z40A2M3A2A1A3S59S58G2S9G0R7A2A2G3A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fimm;Frd;FS;").
Proof using .
  intros * Hi Hsm.
  pose proof (smatch_pcv _ _ _ _ _ Hsm) as Hpc. unfold ms_pc in Hpc.
  eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | | reflexivity |].
  - unfold core_of; cbn [c_pc]. rewrite Hpc. change (sext 64 imm) with (Z_to_bv 64 (bv_signed imm)).
    apply pc_plus.
  - cbn [eval]. unfold core_of; cbn [c_pc]. rewrite Hpc, Z_to_bv64_mod. symmetry. apply pc_plus'.
Qed.

Lemma case_fence : ltac2:(tb__ "0|3|
S26S6Q4A1M0G0G0S6Q5A1M1G1S25S3dS45A1M2S34S46S0S40SeA1S48Vsegs;S23RaA1A2S3fSeS16R9R8R7R6R5A5A2A3S24Vsegs;R5RbS3eG2S3bR4S3cR3R2A2A4A4S57RcS47RcS58S23RcA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fe;Fd;Fc;Fb;Fa;FS;").
Proof using .
  intros * Hi Hsm. eapply step_pc_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto].
Qed.

Lemma case_fencei : ltac2:(tb__ "0|2|
S26S6Q5A1M0G0S6QcA1S25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R8A1A2S3fSeS17R7R6R5A3A2A3S24Vsegs;R5R9S3eG1S3bR4S3cR3R2A2A4A4S57RaS47RaS58S23RaA1Z4A2A2R6R5R4R3A6F_;F_;Fmd;Fms;Ftr;Frho;Fc;Fb;Fa;FS;").
Proof using .
  intros * Hi Hsm. eapply step_pc_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto].
Qed.

Lemma land_m2_mod : ltac2:(tb__ "0|2|
S5eS0S5eS5bS59R1S5aZ2M0Z40A2M1A2S5dG1G0A2A2S59S5bR1N2A2G1A2A3Fz;").
Proof using .
  intro z. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  destruct (Z.lt_ge_cases k 64) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.land_spec.
    f_equal. replace (2 ^ 64 - 2) with ((-2) mod 2 ^ 64) by reflexivity.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia.
    replace (2 ^ 64 - 2) with ((-2) mod 2 ^ 64) by reflexivity.
    rewrite Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r.
Qed.

Lemma jalr_target : ltac2:(tb__ "0|3|
S6Q40M0A1M1S6QcM2A1S5eS0G1S8G0R3S7G0S4cR2A1A2A3S7G0R1A2A3S0G1ScG0S8G0R4S6bG2G0R3A3A3SdG0S6aA2A3S7G0S59S5bR2S5cZ1A1A2S5aZ2Z40A2A2A2A3F_;Ft;Fimm;Fa;").
Proof using .
  intros a imm t H. change (sext 64 imm) with (Z_to_bv 64 (immI imm)). rewrite H.
  apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. change (Z.lnot 1) with (-2).
  change ((Z.lnot (bv_unsigned w1)) mod 2 ^ 64) with (2 ^ 64 - 2).
  rewrite land_m2_mod. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma case_jalr : ltac2:(tb__ "0|3|
S26S6Q5A1M0G0S6QcA1S5eS25S3dS45A1M1S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS19R8R7R6A3A2A3S0S27S52S49RaR8A2S4cR7A1A2S28R6A1A3S24Vsegs;R6RbS3eG1S3bR5S3cR4R3A2A4A4S57RcS47S4aRcRbS28S59S58S23RcA1Z4A2S5aZ2Z40A2M2A2A1A3S59S5bR8S5cZ1A1A2G2A2A2R7R6R5R4A6F_;F_;F_;Fmd;Fms;Ftr;Frho;Ft;Fimm;Frs1;Frd;FS;").
Proof using .
  intros * Hi Ht Hsm.
  pose proof (smatch_pcv _ _ _ _ _ Hsm) as Hpc. unfold ms_pc in Hpc.
  eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | | reflexivity |].
  - apply jalr_target. rewrite (rget_match rho S tr ms md rs1 Hsm).
    rewrite <- mk_addk_sound, Ht. reflexivity.
  - cbn [eval]. unfold core_of; cbn [c_pc]. rewrite Hpc, Z_to_bv64_mod. symmetry. apply pc_plus'.
Qed.

Lemma same_base_eq_sound : ltac2:(tb__ "0|0|
S25S27S27S41S0S40S41A1S56R3R2A2S3fS41R1A2A3S0S41S6cQ40S29R5R4A2S29R5R3A2A3R2A3F_;Fe;Fb;Fa;Frho;").
Proof using .
  intros rho a b e H. unfold same_base_eq in H.
  destruct (split_addr a) as [ba x] eqn:Ha. destruct (split_addr b) as [bb y] eqn:Hb.
  destruct (sv_eqb ba bb) eqn:Heq; [|discriminate]. inversion H; subst e; clear H.
  apply sv_eqb_sound in Heq. subst bb.
  rewrite (split_addr_sound rho a ba x Ha), (split_addr_sound rho b ba y Hb).
  unfold oaddr, bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  set (u := bv_unsigned (eval rho ba)).
  destruct (Z.eqb_spec ((x - y) mod 2 ^ 64) 0) as [E|E].
  - apply Z.eqb_eq. replace (u + x) with ((u + y) + (x - y)) by lia.
    rewrite <- Zplus_mod_idemp_r, E, Z.add_0_r. reflexivity.
  - apply Z.eqb_neq. intros E2. apply E.
    replace (x - y) with ((u + x) - (u + y)) by lia.
    rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, E2, Z.sub_diag. reflexivity.
Qed.

Lemma decide_branch_sound : ltac2:(tb__ "0|1|
S25S26S43S3dS45A1S3bA2S11S27S27S24Vsegs;R6R5R4A4S4bOLx;S4fR6R4R3R2A4S0S41S64R4S29R7R3A2S29R7R2A2A3M0S42A3S0S41G0S44A3S4X4bx3F_;Fb;Fa;Fc;Fw;FS;Frho;").
Proof using .
  intros rho S w c a b Hsm. unfold decide_branch.
  pose proof (smatch_facts _ _ _ Hsm) as Hf.
  set (inner := match fact_lookup (ss_facts S) (SPBranch c a b) with
                | DUnknown_ =>
                    match itv_decide_t (ctx0 (ss_facts S)) c a b with
                    | DUnknown_ => decide_t (mk_dig (ss_facts S)) c a b
                    | d => d
                    end
                | d => d end).
  assert (G : match inner with
              | DTrue => branch_taken c (eval rho a) (eval rho b) = true
              | DFalse => branch_taken c (eval rho a) (eval rho b) = false
              | DUnknown_ => True end).
  { subst inner. pose proof (fact_lookup_sound rho (ss_facts S) (SPBranch c a b) Hf) as L.
    destruct (fact_lookup (ss_facts S) (SPBranch c a b)); cbn in L.
    - exact L.
    - destruct (branch_taken c (eval rho a) (eval rho b)); [exfalso; apply L; reflexivity | reflexivity].
    - pose proof (itv_decide_t_sound rho (ctx0 (ss_facts S)) c a b (ctx0_ok rho _ Hf)) as D0.
      destruct (itv_decide_t (ctx0 (ss_facts S)) c a b); [exact D0 | exact D0 |]. clear D0.
      apply decide_t_sound. apply mk_dig_ok. exact Hf. }
  clearbody inner.
  assert (G2 : match match c, same_base_eq a b with
                     | BC_EQ, Some e => if e then DTrue else DFalse
                     | BC_NE, Some e => if e then DFalse else DTrue
                     | _, _ => inner
                     end with
               | DTrue => branch_taken c (eval rho a) (eval rho b) = true
               | DFalse => branch_taken c (eval rho a) (eval rho b) = false
               | DUnknown_ => True end).
  { destruct c; try exact G; destruct (same_base_eq a b) as [e|] eqn:Hsb; try exact G;
      pose proof (same_base_eq_sound rho a b e Hsb) as E; cbn [branch_taken]; rewrite E;
      destruct e; reflexivity. }
  assert (G3 : match (if sv_eqb a b then match c with BC_EQ | BC_GE | BC_GEU => DTrue | _ => DFalse end
                      else match c, same_base_eq a b with
                     | BC_EQ, Some e => if e then DTrue else DFalse
                     | BC_NE, Some e => if e then DFalse else DTrue
                     | _, _ => inner
                     end) with
               | DTrue => branch_taken c (eval rho a) (eval rho b) = true
               | DFalse => branch_taken c (eval rho a) (eval rho b) = false
               | DUnknown_ => True end).
  { destruct (sv_eqb a b) eqn:E; [|exact G2].
    rewrite (sv_eqb_sound _ _ E). destruct c; cbn [branch_taken]; unfold bv_eqb, bv_lts, bv_ltu;
      rewrite ?Z.eqb_refl, ?Z.ltb_irrefl; reflexivity. }
  destruct a as [x| | | | | | |]; try exact G3. destruct b as [y| | | | | | |]; try exact G3.
  cbn [eval]. destruct (branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y)); reflexivity.
Qed.

Lemma case_branch : ltac2:(tb__ "0|6|
S26S11S6Q5A1M0G0S6QdM1A1S25S3dS45A1M2S34S46S0S40SeA1S48Vsegs;S23R9A1A2S3fSeS15R8R7R6R5A4A2A3S24Vsegs;R5RaS3eG2S3bR4S3cR3R2A2A4A4S49RbR9A2S27S49RcR9A2S27S59S58S23RdA1S9G1R9A2A2S5aZ2Z40A2A2S5eS4bOLx;S4fReRdR3R2A4S57ReS47ReR1A2R9R8R7R6A6S57ReS47ReS58S23ReA1Z4A2M3A2R9R8R7R6A6S5S1S0S41S64RdS29R9R3A2S29R9R2A2A3M4S42A3S57ReS47S4dReS2eRdR3R2A3M5A2R1A2R9R8R7R6A6A2S1S0S41G4S44A3S57ReS47S4dReS2fG5A1A2G3A2R9R8R7R6A6A2A2X4bx3Ttpc;Tb;Ta;F_;F_;Fmd;Fms;Ftr;Frho;Fimm;Frs2;Frs1;Fc;FS;").
Proof using .
  intros S c rs1 rs2 imm rho tr ms md Hi Hsm. cbn zeta.
  pose proof (smatch_pcv _ _ _ _ _ Hsm) as Hpc. unfold ms_pc in Hpc.
  pose proof (decide_branch_sound rho S _ c (get_reg S rs1) (get_reg S rs2) Hsm) as D.
  assert (Hex0 : exec (Z_to_bv 64 4) (Branch c rs1 rs2 imm) (core_of ms)
           = EDone (with_pc (if branch_taken c (rget (core_of ms) rs1) (rget (core_of ms) rs2)
                             then (c_pc (core_of ms) + sext 64 imm)%bv
                             else (c_pc (core_of ms) + Z_to_bv 64 4)%bv) (core_of ms))) by reflexivity.
  rewrite !(rget_match rho S tr ms md _ Hsm) in Hex0.
  change (c_pc (core_of ms)) with (ms_pc_val ms) in Hex0. rewrite Hpc in Hex0.
  change (sext 64 imm) with (Z_to_bv 64 (bv_signed imm)) in Hex0.
  rewrite pc_plus, pc_plus' in Hex0.
  assert (Hbl : sprop_below (ss_next S) (SPBranch c (get_reg S rs1) (get_reg S rs2)) = true).
  { cbn [sprop_below]. rewrite !get_reg_below by (eapply smatch_swf; eauto). reflexivity. }
  destruct (decide_branch S c (get_reg S rs1) (get_reg S rs2)).
  - rewrite D in Hex0. eapply step_pc_sound; [exact Hsm | exact Hi | discriminate | exact Hex0 | reflexivity].
  - rewrite D in Hex0. eapply step_pc_sound; [exact Hsm | exact Hi | discriminate | exact Hex0 | reflexivity].
  - destruct (branch_taken c (eval rho (get_reg S rs1)) (eval rho (get_reg S rs2))) eqn:Hb.
    + left. split; [reflexivity|].
      assert (Hsm1 : smatch segs rho (add_fact S (SPBranch c (get_reg S rs1) (get_reg S rs2))) (tr, mkCfg ms md)).
      { apply smatch_add_fact; [exact Hsm | exact Hbl | exact Hb]. }
      exact (step_pc_sound rho _ tr ms md _ _ _ Hsm1 Hi ltac:(discriminate) Hex0 eq_refl).
    + right. split; [reflexivity|].
      assert (Hsm1 : smatch segs rho (add_fact S (SPNot (SPBranch c (get_reg S rs1) (get_reg S rs2)))) (tr, mkCfg ms md)).
      { apply smatch_add_fact; [exact Hsm | exact Hbl | ]. cbn [holds]. rewrite Hb. discriminate. }
      exact (step_pc_sound rho _ tr ms md _ _ _ Hsm1 Hi ltac:(discriminate) Hex0 eq_refl).
Qed.

End S2.
