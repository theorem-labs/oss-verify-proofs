(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sv"; "ss_pc"; "valuation"; "smatch"; "swf"; "ss_facts"; "ss_fcsr"; "ss_next"; "eval"; "ss_resv"; "fregs_match"; "regs_match"; "sfcsr"; "sprop"; "FcsrFrm0"; "ss_objs"; "sv_below"; "SLit"; "agree_below"; "ss_fregs"; "ss_regs"; "fcsr_match"; "resv_match"; "sobj"; "SPUle"; "freg_sv"; "rw"; "ext_low"; "holds"; "mkVal"; "rd_bytes"; "rl"; "rm"; "sv_eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ffmt"; "csrop"; "Ecall"; "awidth"; "fcvt_ty"; "fmvdir"; "Fcmp"; "Fcvt"; "Sc"; "fcmpop"; "ALU_OR"; "Csr"; "CsrI"; "FLoad"; "FStore"; "Fari"; "Fclass"; "Fma"; "Fminmax"; "Fmv"; "Fsgnj"; "Fsqrt"; "Lr"; "fariop"; "fmaop"; "fminmaxop"; "fsgnop"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "option"; "pair"; "Some"; "snd"; "fst"; "None"; "false"; "prod"; "andb"; "negb"; "app"; "orb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_fregs"; "ms_regs"; "ms_pc_val"; "ms_resv"; "MachineOk"; "machine_result"; "ms_fcsr"; "ms_rom"; "ms_pc"; "ms_svc_pending"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "set_pc"; "fresh"; "set_freg"; "set_reg"; "get_reg"; "frm0b"; "rm_ok"; "addr_aligned"; "StNext"; "amo_log"; "mk_nanbox"; "set_resv"; "step_out"; "sym_csr"; "amo_k"; "fcvt_fty"; "get_freg"; "load_res"; "sym_load"; "LROk"; "add_fact"; "fcvt_ity"; "immI"; "mk_addk"; "mk_ext"; "sym_store"; "regZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "pow"; "modulo"; "eqb"; "lor"; "to_N"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA"; "core_of"; "ms_of"; "@LinuxProcessSemantics.Riscv.Sem"; "core"; "c_regs"; "exec"; "c_pc"; "eff"; "c_fcsr"; "rset"; "EDone"; "c_fregs"; "c_resv"; "resolve_rm"; "with_pc"; "csr_write_illegal"; "nan_box"; "EDefinedIllegal"; "accrue"; "alu64"; "amo_aligned"; "exec_csr"; "fget"; "frm_of"; "fset"; "is_x0"; "slice_get"; "slice_set"; "@LinuxProcessSemantics.Riscv.Prelude"; "bvmap"; "bvmap_set"; "zext"; "@LinuxProcessSemantics.Riscv.Fpu"; "rmode"; "fflags"; "fflags_bits"; "@Stdlib.PArith.BinPos.Pos"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SpecBridge"; "interp_eff0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundF.F"; "ext1"; "ffmt_k"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "step_rel"; "load_post"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "le_bytes_to_word"; "@Stdlib.NArith.BinNat.N"; "mul"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section F.
Variable segs : list Segment.

Lemma smatch_update : ltac2:(tb__ "0|4|
S8S5S4aS65A1M0S57S66S5S57S9Vsegs;R7R6S4cG0S63R5S64R4R3A2A4A4S0S48SaR3A1S49A3S0S28Q40M1A1M2S61R3A1S2aG1S7R4A1A2A3S0S4bG2A1S62R4A1S50G2A1A3S0G2S4bS28Q8A1A1F_;M3S60R5A1S60R8A1A3S0G3S58R6A1S58R9A1A3S11RdR8R7A3S10ReR9R8A3S1bRfScRaA1R9A3S1cR10SfRbA1RaA3S0S4aS1dA1S15RcA1S15R10A1A3S0S4aS13A1SbRdA1SbR11A1A3S9Vsegs;R13ReS4cG0S63R11S64RdRfA2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms';FS';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md S' ms' Hsm Hwf' Hpc' Hpend' Hrom' Hmem' Hr' Hf' Hc' Hv' Ho' Hfa'.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc'|]. split; [exact Hpend'|]. split; [exact Hhalt|].
  split; [intros a; rewrite Hrom'; apply Hrom|].
  split; [intros a Ha; rewrite Hmem'; apply Hroc; exact Ha|].
  split; [exact Hr'|]. split; [exact Hf'|]. split; [exact Hc'|]. split; [exact Hv'|].
  split; [| rewrite Hfa'; exact Hfacts].
  rewrite Ho'. apply (mem_match_same_mem segs rho (ss_objs S) ms); [exact Hmem' | exact Hrom' | exact Hmem].
Qed.

Lemma regs_match_rset_gen : ltac2:(tb__ "0|2|
S8S5S57S57S28Q5M0A1S6S28Q40A1M1S0S48SaR6A1S49A3S11R8R7R5A3S0G1SeR9R4A2R3A3S0SaaG0G1A2S5aR8A1S92S97R6R4S8fR7A1A3A1A3S11RbS6bRaR7R6A3R9A3F_;F_;F_;F_;Fv;Fe;Frd;Fms;Fms';FS;Frho;").
Proof using .
  intros rho S ms' ms rd e v Hwf Hrm Hev Hregs.
  pose proof (regs_match_rset rho S ms rd e v (ms_pc ms) (ms_mem ms) Hwf Hrm Hev) as R.
  intros r Hr. specialize (R r Hr). rewrite Hregs.
  unfold ms_of in R. cbn [ms_regs] in R. exact R.
Qed.

Lemma regs_match_same : ltac2:(tb__ "0|0|
S8S5S5S57S57S11R5R4R2A3S0SaaQ5S28Q40A1A2S5aR2A1S5aR3A1A3S0S4aS6A1S1aR5A1S1aR6A1A3S11R8R6R4A3F_;F_;F_;Fms';Fms;FS';FS;Frho;").
Proof using .
  intros rho S S' ms ms' H Hr Hs r Hr0. rewrite Hr. unfold reg_sv. rewrite Hs. apply H. exact Hr0.
Qed.

Lemma fregs_match_same : ltac2:(tb__ "0|0|
S8S5S5S57S57S10R5R4R2A3S0SaaQ5S28Q40A1A2S59R2A1S59R3A1A3S0S4aS6A1S19R5A1S19R6A1A3S10R8R6R4A3F_;F_;F_;Fms';Fms;FS';FS;Frho;").
Proof using .
  intros rho S S' ms ms' H Hr Hs r. rewrite Hr. unfold freg_sv. rewrite Hs. apply H.
Qed.

Lemma freg_sv_set_freg : ltac2:(tb__ "0|0|
S5S28Q5A1S6S84S0S48SaR4A1S49A3S1S88Z0R2A2S87R2Z20A2A2S0S6S1fS6aR6R5R4A3R3A2S48S6L_;S8bR3S82R5A1A2R4S1fR6R3A2X48x2A3F_;F_;Fr;Fe;Frd;FS;").
Proof using .
  intros S rd e r Hwf Hr. unfold set_freg, freg_sv. cbn [ss_fregs].
  pose proof (regZ_range rd) as Hrd.
  rewrite (nth_list_set (ss_fregs S) (Z.to_nat (regZ rd)) (Z.to_nat r) e (SLit 0))
    by (rewrite (swf_fregs_len S Hwf); lia).
  destruct (Nat.eqb_spec (Z.to_nat r) (Z.to_nat (regZ rd))), (Z.eqb_spec r (regZ rd)); try reflexivity; lia.
Qed.

Lemma fregs_match_fset : ltac2:(tb__ "0|2|
S8S5S57S57S28Q5M0A1S6S28Q40A1M1S0S48SaR6A1S49A3S10R8R7R6A3S0G1SeR9R4A2R3A3S0SaaG0G1A2S59R7A1SabG0G1R6R4S59R8A1A5A3S10RbS6aRaR7R6A3R8A3F_;F_;F_;F_;Fv;Fe;Frd;Fms';Fms;FS;Frho;").
Proof using .
  intros rho S ms ms' rd e v Hwf Hfm Hev Hf r.
  rewrite Hf. pose proof (regZ_range r) as Hr. unfold regZ in Hr.
  rewrite (freg_sv_set_freg S rd e (bv_unsigned r) Hwf Hr).
  rewrite reg_get_set. unfold regZ.
  destruct (bv_eqb r rd) eqn:Hb.
  - unfold bv_eqb in Hb. rewrite Hb. symmetry. exact Hev.
  - unfold bv_eqb in Hb. rewrite Hb. apply Hfm.
Qed.

Lemma next_rel_core1 : ltac2:(tb__ "0|6|
S8S8S5S5S5S4aS65A1M0S57S66S2cS91S9Vsegs;RaR8S4cG0S63R5S64R4R3A2A4A4S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cR3A2A3S2S0S2cR4S2fA3A1S0S5eS52S91S28Q40M1A1M2S4bS28Q8A1A1F_;M3A2M4A1Sb2Vsegs;S93S2aG1Z4A2R5S8fR7A1A3S58R7A1M5A3S5dG4S4cS91G3R4G5A4A2A3S18SdRcA1ReRdA3Sb0SdRdA1SdRbA1A2S9Vsegs;RfRdS4cG0S63RbS64RaR9A2A4A4S0S48SaRdA1S49A3S0G2S94R9A1S2aG1S7ReA1A2A3S11R12RfS90RdRaS58RdA1A3A3S10R13R10S90ReRbS58ReA1A3A3S1bR14ScR11A1S90RfRcS58RfA1A3A3S1cR15SfR12A1S90R10RdS58R10A1A3A3S0S4aS1dA1S15R13A1S15R14A1A3S0S4aS13A1SbR14A1SbR15A1A3S83Vsegs;R17R15R19R14R13R12A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fc';Fi;Fmd;Fms;Ftr;FS';FS1;FS;Frho';Frho;").
Proof using .
  intros rho rho' S S1 S' tr ms md i c' Hsm Hi Hne Hint Hag Hle Hsm1 Hwf' Hpc' Hr' Hf' Hc' Hv' Ho' Hfa'.
  pose proof (smatch_pcv segs _ _ _ _ _ Hsm) as Hpc.
  exists (ms_of ms c' (ms_mem ms)), rho'.
  split.
  { rewrite (step_instr_at segs ms (ss_pc S) i Hpc Hi Hne). rewrite Hint. reflexivity. }
  split; [exact Hag|]. split; [exact Hle|].
  eapply smatch_update; try eassumption; try reflexivity.
Qed.

Lemma next_rel_core : ltac2:(tb__ "0|7|
S8S8S5S5S4aS65A1M0S57S66S2cS91S9Vsegs;R9R7S4cG0S63R5S64R4R3A2A4A4S0S4bS2cA1S67Vsegs;S7R8A1A2S4dS2cR3A2A3S2S0S2cR4S2fA3A1S0S5eS52S91S28Q40M1A1M2S4bS28Q8A1A1F_;M3A2M4A1Sb2Vsegs;S93S2aG1Z4A2R5S8fR7A1A3S58R7A1M5A3S5dG4S4cS91G3R4G5A4A2A3S18SdRbA1M6RdRcA3Sb0SdRcA1G6A2S0S48SaRcA1S49A3S0G2S94R8A1S2aG1S7RdA1A2A3S11R10ReS90RcR9S58RcA1A3A3S10R11RfS90RdRaS58RdA1A3A3S1bR12ScR10A1S90ReRbS58ReA1A3A3S1cR13SfR11A1S90RfRcS58RfA1A3A3S0S4aS1dA1S15R12A1S15R13A1A3S0S4aS13A1SbR13A1SbR14A1A3S83Vsegs;R15R14R17R13R12R11A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fc';Fi;Fmd;Fms;Ftr;FS';FS;Frho';Frho;").
Proof using .
  intros rho rho' S S' tr ms md i c' Hsm Hi Hne Hint Hag Hle Hwf' Hpc' Hr' Hf' Hc' Hv' Ho' Hfa'.
  pose proof (smatch_pcv segs _ _ _ _ _ Hsm) as Hpc.
  exists (ms_of ms c' (ms_mem ms)), rho'.
  split.
  { rewrite (step_instr_at segs ms (ss_pc S) i Hpc Hi Hne). rewrite Hint. reflexivity. }
  split; [exact Hag|]. split; [exact Hle|].
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  eapply smatch_update; try eassumption; try reflexivity.
Qed.

Definition ext1 (rho : valuation) (n : positive) (x : word) : valuation := ltac2:(tb__ "0|0|
S23S85S48S28Q40A1L_;Sb1R1Vn;A2Vx;S20Vrho;R1A2X48x2Li;S25Vrho;A1S26Vrho;A1A3").

Lemma ext1_agree : ltac2:(tb__ "0|0|
S8S85S28Q40A1S18R2R3Sb3R3R2R1A3A3Fx;Fn;Frho;").
Proof using .
  intros rho n x. split; [|split; intros; reflexivity]. intros i Hi. unfold ext1. cbn.
  destruct (Pos.eqb_spec i n); [lia|reflexivity].
Qed.

Lemma ext1_at : ltac2:(tb__ "0|1|
S8S85S28Q40A1M0S0G0S20Sb3R3R2R1A3R2A2R1A3Fx;Fn;Frho;").
Proof using . intros. unfold ext1. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.

Lemma swf_fresh : ltac2:(tb__ "0|0|
S5S0S48SaR1A1S49A3S0S48SaS4eS6S5S69R2A1A3A1S49A3F_;FS;").
Proof using . intros S H. unfold fresh. cbn [snd]. apply (swf_mono_next S). lia. exact H. Qed.

Lemma swf_set_freg : ltac2:(tb__ "0|0|
S5S28Q5A1S6S0S48SaR3A1S49A3S0S48S16SdR4A1R2A2S49A3S0S48SaS6aR5R4R3A3A1S49A3F_;F_;Fe;Frd;FS;").
Proof using .
  intros S rd e Hwf He. pose proof Hwf as W. unfold swf in W |- *.
  unfold set_freg. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  repeat (apply andb_prop in W; destruct W as [W ?]).
  repeat (apply andb_true_intro; split); try assumption.
  - rewrite list_set_length. assumption.
  - apply forallb_list_set; assumption.
Qed.

Lemma fcsr_frm0_bound : ltac2:(tb__ "0|1|
S8S5S4aS65A1M0S57S66S9Vsegs;R5R4S4cG0S63R3S64R2R1A2A4A4S0S12ScR5A1S14A3S87S29Q20S5fR4A1A2Z20A2F_;F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & Hfcsr & _). cbn [fst snd cfg_ms] in Hfcsr.
  rewrite Hf in Hfcsr. exact Hfcsr.
Qed.

Lemma havoc_freg_sound : ltac2:(tb__ "0|8|
S8S5S4aS65A1M0S57S66S2cS28Q5M1A1S91S28Q40M2A1M3S9Vsegs;R9R8S4cG0S63R7S64R6R5A2A4A4S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cR5A2A3S2S0S2cR6S2fA3A1S0S95S93S2aG2Z4M4A2M5R7S8fR9A1A3S98R5A1A3S0SaaG1G3A2M6S92R6A1S5aRaA1A3S0G6S99R7A1SabG1G3R8R6S59RbA1A5A3S0G3S94R8A1S2bG2S5bRcA1G5A3A3S0S4bG3A1S9aR9A1S5cRdA1A3S0S12ScR10A1S14A3S87S29Q20S96RbA1A2Z20A2S83Vsegs;R12S68S6aS4eS6S5S69R12A1M7A3RdS4fS6S5G7A3A3S86S7R12A1G4A2A2R13R11R10RfA7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FVAL;Fc';Frd;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i rd c' VAL Hsm Hi Hne Hex Hregs Hfregs Hpcc Hresv Hfrm Hf'.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (rho' := ext1 rho (ss_next S) VAL).
  pose proof (ext1_agree rho (ss_next S) VAL) as Hag.
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  destruct Hsm1 as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply (next_rel_core rho rho'); try eassumption.
  - rewrite Hex. reflexivity.
  - cbn. lia.
  - rewrite swf_set_pc. apply swf_set_freg; [apply swf_fresh; exact Hwf|]. cbn. apply Pos.ltb_lt. lia.
  - cbn [ss_pc set_pc]. unfold ms_pc in Hpc. rewrite Hpcc, Hpc. apply pc_plus'.
  - eapply regs_match_same; [exact Hr1 | cbn; exact Hregs | reflexivity].
  - unfold set_pc. cbn [ss_fregs].
    eapply (fregs_match_fset rho' (snd (fresh S)) ms); [apply swf_fresh; exact Hwf | | | cbn; exact Hfregs].
    + eapply fregs_match_same; [exact Hfr1 | reflexivity | reflexivity].
    + cbn. unfold rho'. apply ext1_at.
  - cbn [ss_fcsr set_pc set_freg fresh snd]. rewrite Hfrm. cbn. exact Hf'.
  - cbn [ss_resv set_pc set_freg fresh snd]. unfold resv_match in Hv1 |- *. cbn [ms_resv ms_of]. rewrite Hresv. exact Hv1.
  - reflexivity.
  - reflexivity.
Qed.

Lemma havoc_reg_sound : ltac2:(tb__ "0|8|
S8S5S4aS65A1M0S57S66S2cS28Q5M1A1S91S28Q40M2A1M3S9Vsegs;R9R8S4cG0S63R7S64R6R5A2A4A4S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cR5A2A3S2S0S2cR6S2fA3A1S0S95S93S2aG2Z4M4A2M5R7S8fR9A1A3S98R5A1A3S0SaaG1G3A2M6S92R6A1S92S97R7R5S8fRaA1A3A1A3S0G6S99R7A1S59RbA1A3S0G3S94R8A1S2bG2S5bRcA1G5A3A3S0S4bG3A1S9aR9A1S5cRdA1A3S0S12ScR10A1S14A3S87S29Q20S96RbA1A2Z20A2S83Vsegs;R12S68S6bS4eS6S5S69R12A1M7A3RdS4fS6S5G7A3A3S86S7R12A1G4A2A2R13R11R10RfA7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FVAL;Fc';Frd;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i rd c' VAL Hsm Hi Hne Hex Hregs Hfregs Hpcc Hresv Hfrm Hf'.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (rho' := ext1 rho (ss_next S) VAL).
  pose proof (ext1_agree rho (ss_next S) VAL) as Hag.
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  destruct Hsm1 as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply (next_rel_core rho rho'); try eassumption.
  - rewrite Hex. reflexivity.
  - cbn. rewrite ss_next_set_reg. cbn. lia.
  - rewrite swf_set_pc. apply swf_set_reg; [apply swf_fresh; exact Hwf|]. cbn. apply Pos.ltb_lt. lia.
  - cbn [ss_pc set_pc]. unfold ms_pc in Hpc. rewrite Hpcc, Hpc. apply pc_plus'.
  - eapply (regs_match_same rho' (set_reg (snd (fresh S)) rd (fst (fresh S)))); [| reflexivity | reflexivity].
    eapply (regs_match_rset_gen rho' (snd (fresh S)) _ ms); [apply swf_fresh; exact Hwf | | | cbn; exact Hregs].
    + eapply regs_match_same; [exact Hr1 | reflexivity | reflexivity].
    + cbn. unfold rho'. apply ext1_at.
  - eapply fregs_match_same; [exact Hfr1 | cbn; exact Hfregs |].
    cbn [ss_fregs set_pc]. rewrite ss_fregs_set_reg. reflexivity.
  - cbn [ss_fcsr set_pc]. rewrite ss_fcsr_set_reg. cbn [fresh snd ss_fcsr]. rewrite Hfrm. cbn. exact Hf'.
  - cbn [ss_resv set_pc]. rewrite ss_resv_set_reg. cbn [fresh snd ss_resv].
    unfold resv_match in Hv1 |- *. cbn [ms_resv ms_of]. rewrite Hresv. exact Hv1.
  - cbn [ss_objs set_pc]. rewrite ss_objs_set_reg. reflexivity.
  - cbn [ss_facts set_pc]. rewrite ss_facts_set_reg. reflexivity.
Qed.

Lemma havoc_reg_b_sound : ltac2:(tb__ "0|a|
S8S5S4aS65A1M0S57S66S2cS28Q5M1A1S91S28Q40M2A1M3S9Vsegs;R9R8S4cG0S63R7S64R6R5A2A4A4S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cR5A2A3S2S0S2cR6S2fA3A1S0S95S93S2aG2Z4M4A2M5R7S8fR9A1A3S98R5A1A3S0SaaG1G3A2M6S92R6A1S92S97R7R5S8fRaA1A3A1A3S0G6S99R7A1S59RbA1A3S0G3S94R8A1S2bG2S5bRcA1G5A3A3S0S4bG3A1S9aR9A1S5cRdA1A3S0S12ScR10A1S14A3S87S29Q20S96RbA1A2Z20A2S88S29G2RbA2Z1M7A2S83Vsegs;R13S68S6bS7cS4eS6S5S69R13A1M8A3S1eS4fS6S5G8A3M9S17G7A1A2A2ReG9A3S86S7R13A1G4A2A2R14R12R11R10A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FVAL;Fc';Frd;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i rd c' VAL Hsm Hi Hne Hex Hregs Hfregs Hpcc Hresv Hfrm Hf' Hval.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (rho' := ext1 rho (ss_next S) VAL).
  pose proof (ext1_agree rho (ss_next S) VAL) as Hag.
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  set (S1 := add_fact (snd (fresh S)) (SPUle (fst (fresh S)) (SLit 1))).
  assert (HsmF : smatch segs rho' (snd (fresh S)) (tr, mkCfg ms md)).
  { destruct Hsm1 as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hr1 & Hfr1 & Hc1 & Hv1 & Hm1 & Hfa1).
    unfold smatch. cbn [fst snd cfg_ms cfg_model fresh ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    split; [apply swf_fresh; exact Hwf|]. repeat (split; [assumption|]). exact Hfa1. }
  assert (Hsm2 : smatch segs rho' S1 (tr, mkCfg ms md)).
  { unfold S1. apply smatch_add_fact; [exact HsmF| |].
    - cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia.
    - cbn [holds eval fst fresh]. unfold rho'. rewrite ext1_at. change (bv_unsigned (Z_to_bv 64 1)) with 1. exact Hval. }
  pose proof (smatch_swf segs _ _ _ Hsm2) as Hwf2.
  pose proof Hsm2 as Hsm3. destruct Hsm3 as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply (next_rel_core1 rho rho' S S1); try eassumption.
  - rewrite Hex. reflexivity.
  - cbn. rewrite ss_next_set_reg. cbn. lia.
  - rewrite swf_set_pc. apply swf_set_reg; [exact Hwf2|]. cbn. apply Pos.ltb_lt. lia.
  - cbn [ss_pc set_pc]. unfold ms_pc in Hpc. rewrite Hpcc, Hpc. apply pc_plus'.
  - eapply (regs_match_same rho' (set_reg S1 rd (fst (fresh S)))); [| reflexivity | reflexivity].
    eapply (regs_match_rset_gen rho' S1 _ ms); [exact Hwf2 | | | cbn; exact Hregs].
    + eapply regs_match_same; [exact Hr1 | reflexivity | reflexivity].
    + cbn. unfold rho'. apply ext1_at.
  - eapply fregs_match_same; [exact Hfr1 | cbn; exact Hfregs |].
    cbn [ss_fregs set_pc]. rewrite ss_fregs_set_reg. reflexivity.
  - cbn [ss_fcsr set_pc]. rewrite ss_fcsr_set_reg. cbn [S1 add_fact fresh snd ss_fcsr]. rewrite Hfrm. cbn. exact Hf'.
  - cbn [ss_resv set_pc]. rewrite ss_resv_set_reg. cbn [S1 add_fact fresh snd ss_resv].
    unfold resv_match in Hv1 |- *. cbn [ms_resv ms_of]. rewrite Hresv. exact Hv1.
  - cbn [ss_objs set_pc]. rewrite ss_objs_set_reg. reflexivity.
  - cbn [ss_facts set_pc]. rewrite ss_facts_set_reg. reflexivity.
Qed.

Lemma frm_of_zero : ltac2:(tb__ "0|0|
S57S87S29Q20S5fR1A1A2Z20A2S0S84Sa5S8fR2A1A1Z0A3F_;Fms;").
Proof using .
  intros ms H. unfold frm_of, core_of. cbn [c_fcsr].
  pose proof (bv_unsigned_in_range _ (ms_fcsr ms)) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma rm_ok_resolve : ltac2:(tb__ "0|1|
S8S5S4aS65A1M0S57S66S28Q3A1S9Vsegs;R6R5S4cG0S63R4S64R3R2A2A4A4S0S48S6eR6R2A2S49A3S1S0S12ScR7A1S14A3S3SadSadS0S4bSadA1S9bR4S8fR6A1A2S4dSadR1A2A3LMD;A2A2F_;F_;Frm;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md rm Hsm Hok. unfold rm_ok in Hok.
  destruct (ss_fcsr S) eqn:Hf; [|discriminate]. split; [reflexivity|].
  pose proof (fcsr_frm0_bound rho S tr ms md Hsm Hf) as Hb.
  unfold resolve_rm. rewrite (frm_of_zero ms Hb). unfold rmode_of_field.
  pose proof (bv_unsigned_in_range _ rm) as R. change (bv_modulus 3) with 8 in R.
  apply Bool.orb_true_iff in Hok. destruct Hok as [Hok|Hok].
  - apply Z.leb_le in Hok.
    destruct (Z.eqb_spec (bv_unsigned rm) 7); [lia|]. unfold rmode_of_Z.
    destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|]. lia.
  - apply Z.eqb_eq in Hok. rewrite Hok. cbn. eexists; reflexivity.
Qed.

Lemma resolve_rm_with_pc : ltac2:(tb__ "0|0|
S28Q3A1S28Q40A1S91S0S4bSadA1S9bR3S9cR2R1A2A2S9bR3R1A2A3Fc;Fp;Frm;").
Proof using . intros. reflexivity. Qed.

Lemma fflags_bits_range : ltac2:(tb__ "0|1|
SaeS1S88Z0SafR1A1M0A2S87G0Z20A2A2Ffl;").
Proof using . intros [[|] [|] [|] [|] [|]]; (split; [vm_compute; discriminate | vm_compute; reflexivity]). Qed.

Lemma lor_lt_pow2 : ltac2:(tb__ "0|4|
S84S84S84S1S88Z0M0R3A2M1S87R3S89Z2M2R1A2A2A2S1G1S87R3S89G2R2A2A2A2G1S1S88G0S8cR6R5A2M3A2S87G3S89G2R4A2A2A2F_;F_;F_;Fn;Fb;Fa;").
Proof using .
  intros a b n Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (H1 : Z.lor a b <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia).
  apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma accrue_bound : ltac2:(tb__ "0|2|
S28Q20M0A1SaeS87S29G0R2A2Z20M1A2S87S29G0S2aG0S8cS29G0R3A2SafR2A1A2A2A2G1A2F_;Ffl;Ff;").
Proof using .
  intros f fl Hf. pose proof (bv_unsigned_in_range _ f) as R. pose proof (fflags_bits_range fl) as Rfl.
  pose proof (lor_lt_pow2 (bv_unsigned f) (fflags_bits fl) 5 ltac:(change (2^5) with 32; lia) ltac:(change (2^5) with 32; lia) ltac:(lia)) as L.
  change (2 ^ 5) with 32 in L.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma accrue_fcsr : ltac2:(tb__ "0|2|
SaeS91S87S29Q20M0S96R1A1A2Z20M1A2S87S29G0S96Sa0R3R2A2A1A2G1A2F_;Fc;Ffl;").
Proof using . intros fl c H. unfold accrue, with_fcsr. cbn [c_fcsr]. apply accrue_bound. exact H. Qed.

Ltac havoc_freg_tac Hsm Hi :=
  eapply (havoc_freg_sound _ _ _ _ _ _ _ _ _ Hsm Hi); [discriminate | | reflexivity | reflexivity | reflexivity | reflexivity | | ].

Lemma case_fari : ltac2:(tb__ "0|3|
S5S44S2dS28Q5A1M0G0G0S28Q3A1S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RbA1A2S4dS2cS3cRaR9R8R7R6R5A6A2A3S9Vsegs;R5RcS4cG1S63R4S64R3R2A2A4A4S0S48S6eRdR7A2S49A3S83Vsegs;ReS68S6aS4eS6S5S69ReA1M2A3RbS4fS6S5G2A3A3S86S7ReA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frm;Frs2;Frs1;Frd;Ffmt;Fop;FS;").
Proof using .
  intros * Hi Hsm Hok.
  destruct (rm_ok_resolve _ _ _ _ _ _ Hsm Hok) as [Hfrm [MD HMD]].
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fari op fmt rd rs1 rs2 rm) (core_of ms) = EDone c'
            /\ c_regs c' = ms_regs ms /\ c_fregs c' = bvmap_set rd VAL (ms_fregs ms)
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. rewrite resolve_rm_with_pc, HMD.
    destruct (match op with F_ADD => _ | F_SUB => _ | F_MUL => _ | F_DIV => _ end) as [v fl].
    destruct fmt; (eexists _, _; split; [reflexivity|]; cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_freg_sound; eauto; discriminate.
Qed.

Lemma frm0b_sound : ltac2:(tb__ "0|0|
S5S0S48S6dR1A1S49A3S0S12ScR2A1S14A3F_;FS;").
Proof using . intros S H. unfold frm0b in H. destruct (ss_fcsr S); [reflexivity|discriminate]. Qed.

Lemma c_regs_rset : ltac2:(tb__ "0|3|
S28Q5M0A1S28Q40A1M1S91S57S0SaaG0G1A2M2S92R2A1S5aR1A1A3S0G2S92S97R5R4R3A3A1S92S97R5R4S8fR2A1A3A1A3F_;Fms;Fc;FV;Frd;").
Proof using . intros rd V c ms H. unfold rset, with_regs, core_of. destruct (is_x0 rd); cbn; rewrite ?H; reflexivity. Qed.

Lemma case_fsqrt : ltac2:(tb__ "0|3|
S5S2dS28Q5A1M0G0S28Q3A1S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cS42R8R7R6R5A4A2A3S9Vsegs;R5RaS4cG1S63R4S64R3R2A2A4A4S0S48S6eRbR7A2S49A3S83Vsegs;RcS68S6aS4eS6S5S69RcA1M2A3RaS4fS6S5G2A3A3S86S7RcA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frm;Frs1;Frd;Ffmt;FS;").
Proof using .
  intros * Hi Hsm Hok.
  destruct (rm_ok_resolve _ _ _ _ _ _ Hsm Hok) as [Hfrm [MD HMD]].
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fsqrt fmt rd rs1 rm) (core_of ms) = EDone c'
            /\ c_regs c' = ms_regs ms /\ c_fregs c' = bvmap_set rd VAL (ms_fregs ms)
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. rewrite resolve_rm_with_pc, HMD.
    destruct (fp_sqrt _ _ _) as [v fl].
    destruct fmt; (eexists _, _; split; [reflexivity|]; cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_freg_sound; eauto; discriminate.
Qed.

Lemma case_fma : ltac2:(tb__ "0|3|
S5S45S2dS28Q5A1M0G0G0G0S28Q3A1S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RcA1A2S4dS2cS3eRbRaR9R8R7R6R5A7A2A3S9Vsegs;R5RdS4cG1S63R4S64R3R2A2A4A4S0S48S6eReR7A2S49A3S83Vsegs;RfS68S6aS4eS6S5S69RfA1M2A3RcS4fS6S5G2A3A3S86S7RfA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frm;Frs3;Frs2;Frs1;Frd;Ffmt;Fop;FS;").
Proof using .
  intros * Hi Hsm Hok.
  destruct (rm_ok_resolve _ _ _ _ _ _ Hsm Hok) as [Hfrm [MD HMD]].
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fma op fmt rd rs1 rs2 rs3 rm) (core_of ms) = EDone c'
            /\ c_regs c' = ms_regs ms /\ c_fregs c' = bvmap_set rd VAL (ms_fregs ms)
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. rewrite resolve_rm_with_pc, HMD.
    destruct op; destruct (fp_fma _ _ _ _ _) as [v fl];
    destruct fmt; (eexists _, _; split; [reflexivity|]; cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_freg_sound; eauto; discriminate.
Qed.

Lemma case_fminmax : ltac2:(tb__ "0|3|
S5S46S2dS28Q5A1M0G0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS3fR9R8R7R6R5A5A2A3S9Vsegs;R5RbS4cG1S63R4S64R3R2A2A4A4S0S48S6dRcA1S49A3S83Vsegs;RdS68S6aS4eS6S5S69RdA1M2A3RaS4fS6S5G2A3A3S86S7RdA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Ffmt;Fop;FS;").
Proof using .
  intros * Hi Hsm Hok. pose proof (frm0b_sound S Hok) as Hfrm.
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fminmax op fmt rd rs1 rs2) (core_of ms) = EDone c'
            /\ c_regs c' = ms_regs ms /\ c_fregs c' = bvmap_set rd VAL (ms_fregs ms)
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. destruct (fp_minmax _ _ _ _) as [v fl].
    destruct fmt; (eexists _, _; split; [reflexivity|]; cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_freg_sound; eauto; discriminate.
Qed.

Lemma case_fsgnj : ltac2:(tb__ "0|3|
S5S47S2dS28Q5A1M0G0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS41R9R8R7R6R5A5A2A3S9Vsegs;R5RbS4cG1S63R4S64R3R2A2A4A4S0S48S6dRcA1S49A3S83Vsegs;RdS68S6aS4eS6S5S69RdA1M2A3RaS4fS6S5G2A3A3S86S7RdA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Ffmt;Fop;FS;").
Proof using .
  intros * Hi Hsm Hok. pose proof (frm0b_sound S Hok) as Hfrm.
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fsgnj op fmt rd rs1 rs2) (core_of ms) = EDone c'
            /\ c_regs c' = ms_regs ms /\ c_fregs c' = bvmap_set rd VAL (ms_fregs ms)
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. destruct fmt; (eexists _, _; split; [reflexivity|]; cbn; repeat split; try reflexivity; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_freg_sound; eauto; discriminate.
Qed.

Lemma case_fcmp : ltac2:(tb__ "0|3|
S5S36S2dS28Q5A1M0G0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS33R9R8R7R6R5A5A2A3S9Vsegs;R5RbS4cG1S63R4S64R3R2A2A4A4S0S48S6dRcA1S49A3S83Vsegs;RdS68S6bS4eS6S5S69RdA1M2A3RaS4fS6S5G2A3A3S86S7RdA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Ffmt;Fop;FS;").
Proof using .
  intros * Hi Hsm Hok. pose proof (frm0b_sound S Hok) as Hfrm.
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fcmp op fmt rd rs1 rs2) (core_of ms) = EDone c'
            /\ c_regs c' = c_regs (rset rd VAL (core_of ms)) /\ c_fregs c' = ms_fregs ms
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. destruct (match op with F_EQ => _ | F_LT => _ | F_LE => _ end) as [v fl].
    eexists _, (if v then w1 else w0). split; [reflexivity|].
    split; [apply c_regs_rset; reflexivity|].
    unfold rset; destruct (is_x0 rd); cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb. }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_reg_sound; eauto; discriminate.
Qed.

Lemma case_fcmp_b : ltac2:(tb__ "0|4|
S5S36S2dS28Q5A1M0G0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS33R9R8R7R6R5A5A2A3S9Vsegs;R5RbS4cG1S63R4S64R3R2A2A4A4S0S48S6dRcA1S49A3S83Vsegs;RdS68S6bS7cS4eS6S5S69RdA1M2A3S1eS4fS6S5G2A3M3S17Z1A1A2A2RaG3A3S86S7RdA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Ffmt;Fop;FS;").
Proof using .
  intros * Hi Hsm Hok. pose proof (frm0b_sound S Hok) as Hfrm.
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fcmp op fmt rd rs1 rs2) (core_of ms) = EDone c'
            /\ c_regs c' = c_regs (rset rd VAL (core_of ms)) /\ c_fregs c' = ms_fregs ms
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32
            /\ bv_unsigned VAL <= 1).
  { cbn [exec]. destruct (match op with F_EQ => _ | F_LT => _ | F_LE => _ end) as [v fl].
    eexists _, (if v then w1 else w0). split; [reflexivity|].
    split; [apply c_regs_rset; reflexivity|].
    unfold rset; destruct (is_x0 rd); destruct v; cbn; repeat split; try reflexivity; try apply accrue_bound; try exact Hb;
      vm_compute; discriminate. }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5 & H6).
  eapply havoc_reg_b_sound; eauto; discriminate.
Qed.

Lemma case_fclass : ltac2:(tb__ "0|3|
S5S2dS28Q5A1M0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7R8A1A2S4dS2cS3dR7R6R5A3A2A3S9Vsegs;R5R9S4cG1S63R4S64R3R2A2A4A4S0S48S6dRaA1S49A3S83Vsegs;RbS68S6bS4eS6S5S69RbA1M2A3R9S4fS6S5G2A3A3S86S7RbA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Frs1;Frd;Ffmt;FS;").
Proof using .
  intros * Hi Hsm Hok. pose proof (frm0b_sound S Hok) as Hfrm.
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fclass fmt rd rs1) (core_of ms) = EDone c'
            /\ c_regs c' = c_regs (rset rd VAL (core_of ms)) /\ c_fregs c' = ms_fregs ms
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. eexists _, _. split; [reflexivity|].
    split; [apply c_regs_rset; reflexivity|].
    unfold rset; destruct (is_x0 rd); cbn; repeat split; try reflexivity; exact Hb. }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_reg_sound; eauto; discriminate.
Qed.

Lemma case_fcvt_f : ltac2:(tb__ "0|3|
S5S31S31S28Q5A1M0G0S28Q3A1S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS34R9R8R7R6R5A5A2A3S9Vsegs;R5RbS4cG1S63R4S64R3R2A2A4A4S0S48S6eRcR7A2S49A3S0S48S53S77RcA1S56S77RbA1S7dRbA1A2A2S49A3S83Vsegs;ReS68S6aS4eS6S5S69ReA1M2A3RbS4fS6S5G2A3A3S86S7ReA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Frm;Frs1;Frd;Fsrc;Fdst;FS;").
Proof using .
  intros * Hi Hsm Hok Hty.
  destruct (rm_ok_resolve _ _ _ _ _ _ Hsm Hok) as [Hfrm [MD HMD]].
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fcvt dst src rd rs1 rm) (core_of ms) = EDone c'
            /\ c_regs c' = ms_regs ms /\ c_fregs c' = bvmap_set rd VAL (ms_fregs ms)
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. rewrite resolve_rm_with_pc, HMD.
    destruct dst, src; cbn [fcvt_fty fcvt_ity andb orb] in Hty; try discriminate; cbn [andb];
      first [ destruct (fp_convert _ _ _ _) as [v fl] | destruct (fp_of_int _ _ _ _ _) as [v fl] ];
      (eexists _, _; split; [reflexivity|]; cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_freg_sound; eauto; discriminate.
Qed.

Lemma case_fcvt_i : ltac2:(tb__ "0|3|
S5S31S31S28Q5A1M0G0S28Q3A1S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS34R9R8R7R6R5A5A2A3S9Vsegs;R5RbS4cG1S63R4S64R3R2A2A4A4S0S48S6eRcR7A2S49A3S0S48S53S7dRcA1S77RbA1A2S49A3S83Vsegs;ReS68S6bS4eS6S5S69ReA1M2A3RbS4fS6S5G2A3A3S86S7ReA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Frm;Frs1;Frd;Fsrc;Fdst;FS;").
Proof using .
  intros * Hi Hsm Hok Hty.
  destruct (rm_ok_resolve _ _ _ _ _ _ Hsm Hok) as [Hfrm [MD HMD]].
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  assert (E : exists c' VAL, exec (Z_to_bv 64 4) (Fcvt dst src rd rs1 rm) (core_of ms) = EDone c'
            /\ c_regs c' = c_regs (rset rd VAL (core_of ms)) /\ c_fregs c' = ms_fregs ms
            /\ c_pc c' = (ms_pc_val ms + Z_to_bv 64 4)%bv /\ c_resv c' = ms_resv ms /\ bv_unsigned (c_fcsr c') < 32).
  { cbn [exec]. rewrite resolve_rm_with_pc, HMD.
    destruct dst, src; cbn [fcvt_fty fcvt_ity andb orb] in Hty; try discriminate; cbn [andb];
      destruct (fp_to_int _ _ _ _ _) as [v fl];
      (eexists _, _; split; [reflexivity|]; split; [apply c_regs_rset; reflexivity|];
       unfold rset; destruct (is_x0 rd); cbn; repeat split; try reflexivity; apply accrue_bound; exact Hb). }
  destruct E as (c' & VAL & Hex & H1 & H2 & H3 & H4 & H5).
  eapply havoc_reg_sound; eauto; discriminate.
Qed.

Lemma fget_match : ltac2:(tb__ "0|1|
S8S5S4aS65A1M0S57S66S28Q5A1S9Vsegs;R6R5S4cG0S63R4S64R3R2A2A4A4S0S28Q40A1Sa4S8fR4A1R2A2SeR7S78R6R2A2A2A3F_;Fr;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md r Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & Hfregs & _). cbn [fst snd cfg_ms] in Hfregs.
  unfold fget, core_of, get_freg. cbn [c_fregs]. apply Hfregs.
Qed.

Lemma nan_box_or : ltac2:(tb__ "0|2|
S28Q20M0A1S0S28Q40M1A1S9eR1A1Sa1S37SacG0G1R1A3S2aG1Zffffffff00000000A2A3A3Fv;").
Proof using .
  intros v. apply bv_eq. unfold nan_box, alu64, alu, zext.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_or_unsigned, bv_zero_extend_unsigned by (cbn; lia).
  rewrite !Z_to_bv_unsigned. cbn [bv_wrap bv_modulus].
  change (bv_wrap 32 (-1)) with 4294967295.
  change (Z.of_N 32) with 32. rewrite Z.shiftl_mul_pow2 by lia.
  change (4294967295 * 2 ^ 32) with 18446744069414584320.
  change (bv_wrap 64 18446744069414584320) with 18446744069414584320.
  apply Z.lor_comm.
Qed.

Lemma mk_nanbox_sound : ltac2:(tb__ "0|3|
S8S6S28Q20M0A1S0S28Q40M1A1M2SeR3R2A2SacG0G1R1A3A3S0G2SeR4S72R3A1A2S9eR2A1A3F_;Fv;Fe;Frho;").
Proof using . intros rho e v H. unfold mk_nanbox. rewrite mk_alu_sound, H, nan_box_or. reflexivity. Qed.

Lemma mk_nanbox_below : ltac2:(tb__ "0|0|
S85S6S0S48S16R2R1A2S49A3S0S48S16R3S72R2A1A2S49A3F_;Fe;Fn;").
Proof using . intros. unfold mk_nanbox. apply mk_alu_below; [assumption|reflexivity]. Qed.

Lemma step_frd_sound : ltac2:(tb__ "0|6|
S8S5S4aS65A1M0S57S66S2cS28Q5A1S28Q40M1A1M2S6S9Vsegs;R9R8S4cG0S63R7S64R6R5A2A4A4S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cR5A2A3S2S0S2cR6S2fA3A1S0S95S93S2aG1Z4M3A2M4R7S8fR9A1M5A3S98Sa6R6R5S9cS2bG1S5bR9A1G4A3G5A2A3A1A3S0S48S16SdRcA1R5A2S49A3S0G2SeReR6A2R7A3S83Vsegs;ReS68S6aReR9R7A3S86S7ReA1G3A2A2RfRdRcRbA7F_;F_;F_;F_;F_;F_;Fe;Fv;Frd;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i rd v e Hsm Hi Hne Hex He Hev.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof Hsm as Hsm0.
  destruct Hsm as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply (next_rel_core rho rho); try eassumption.
  - rewrite Hex. reflexivity.
  - apply agree_below_refl.
  - cbn. lia.
  - rewrite swf_set_pc. apply swf_set_freg; assumption.
  - cbn [ss_pc set_pc]. unfold ms_pc in Hpc. rewrite Hpc. apply pc_plus'.
  - eapply regs_match_same; [exact Hr1 | reflexivity | reflexivity].
  - unfold set_pc. cbn [ss_fregs]. eapply (fregs_match_fset rho S ms); [exact Hwf | exact Hfr1 | exact Hev | reflexivity].
  - cbn. exact Hc1.
  - cbn. unfold resv_match in Hv1 |- *. cbn [ms_resv ms_of]. exact Hv1.
  - reflexivity.
  - reflexivity.
Qed.

Lemma case_fmv : ltac2:(tb__ "0|7|
S5S32S2dS28Q5A1M0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7R9A1A2S4dS2cS40R8R7R6R5A4A2A3S9Vsegs;R5RaS4cG1S63R4S64R3R2A2A4A4S83Vsegs;RbS32S5Ldir;RaS2dS5Lfmt;M2R9S68S6bRbR8S80S49Q20M3S78RbR7A2M4A3A3S86S7RbA1Z4A2M5A2S68S6bRbR8G4A3G5A2X2dx2G2R9S68S6aRbR8S72S80S51G3S6cRbR7A2M6A3A1A3G5A2S68S6aRbR8G6A3G5A2X2dx2X32x2R6R5R4R3A7F_;F_;Fmd;Fms;Ftr;Frho;Frs1;Frd;Ffmt;Fdir;FS;").
Proof using .
  intros * Hi Hsm. pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct dir, fmt.
  - eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | |].
    + apply mk_ext_below. apply get_freg_below. exact Hwf.
    + rewrite mk_ext_sound, <- (fget_match rho S tr ms md rs1 Hsm). reflexivity.
  - eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | |].
    + apply get_freg_below. exact Hwf.
    + rewrite <- (fget_match rho S tr ms md rs1 Hsm). reflexivity.
  - eapply step_frd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | |].
    + apply mk_nanbox_below, mk_ext_below, get_reg_below. exact Hwf.
    + apply mk_nanbox_sound. rewrite mk_ext_sound, <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity.
  - eapply step_frd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | |].
    + apply get_reg_below. exact Hwf.
    + rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity.
Qed.

Lemma load_post_proj : ltac2:(tb__ "0|8|
S5S8S57S28Q40A1M0S84S48S6S5S4aS65A1M1S66Sb6Vsegs;RaR9R8R7R6R5R4R3R2R1AbS3S4aS28Q8M2A1A1M3G3S3S8S8S1S0S4bG3A1S24RbRaS8eR9A1A3S4dG3R2A2A3S1S18SdRdA1M4RcR1A3S1Sb0G4SdR6A1M5A2S1S9Vsegs;R1R6S4cG1S63R5S64RbR4A2A4A4S1S0G0SeR1R7A2S21R8Sb9G2S8dR9A1A2Sb8R2A1A3A3S1S0S48S16G5R7A2S49A3S1S0S84S7R6A1S7RdA1A3S1S0S4aS6A1M6S1aR6A1S1aRdA1A3S1S0G6S19R6A1S19RdA1A3S1S0S12ScR6A1ScRdA1A3S1S0S4bS6A1SfR6A1SfRdA1A3S3S4aS13A1M7G7S0G7SbR7A1S55S13R1SbReA1A3A3LF;A2A2A2A2A2A2A2A2A2A2A2A2Lrho';A2Lbs;A2F_;Fmd;Ftr;FS';Fv;Fsgn;Fk;Fa;Fms;Frho;FS;").
Proof using . intros. exact H. Qed.

Lemma case_fload : ltac2:(tb__ "0|5|
S5S2dS28Q5A1M0G0S28QcA1S6S5S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RbA1A2S4dS2cS3aRaR9R8R7A4A2A3S2dOLfmt;RbS0S79S7aVsegs;RcS7fS6cRcR9A2S7eR8A1A2M2Z4M3S51A5S7bR7R6A2M4A3S0S79S7aVsegs;RcG2Z8S49A5G4A3X2dx2S9Vsegs;R6RdS4cG1S63R5S64R4R3A2A4A4Sb5Vsegs;ReS68S6aR8RcS2dS6Lfmt;RdS72R9A1R9X2dx2A3S86S7ReA1G3A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fv;Fimm;Frs1;Frd;Ffmt;FS;").
Proof using .
  intros S fmt rd rs1 imm v S' rho tr ms md Hi Hload Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  assert (Hae : sv_below (ss_next S) (mk_addk (get_reg S rs1) (immI imm)) = true).
  { apply mk_addk_below. apply get_reg_below. exact Hwf. }
  assert (Hrom : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & Hrom & _); exact Hrom).
  pose proof Hsm as Hsm0.
  destruct Hsm0 as (_ & Hpc & _ & _ & _ & _ & _ & _ & _ & _ & _).
  cbn [fst snd cfg_ms cfg_model] in Hpc.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho (mk_addk (get_reg S rs1) (immI imm))).
  { rewrite mk_addk_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity. }
  destruct fmt.
  -
    destruct (sym_load_sound_gen segs rho S tr ms md _ 4 false v S' Hsm Hae ltac:(lia) Hload) as [(Hlen & Hrd & _ & _) | HLP].
    { left. split; [exact Hlen|]. rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
      rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
      cbn [exec]. cbn [interp_eff0 width_bytes]. rewrite Haddr.
      change (Z.to_nat 4) with 4%nat in Hrd. rewrite Hrd. reflexivity. }
    right.
    destruct (load_post_proj _ _ _ _ _ _ _ _ _ _ HLP)
      as (bs & rho' & Hrd & Hag & Hnext & Hsm' & Hev & Hbelow & Hpc' & Hregs' & Hfregs' & Hfcsr' & Hresv' & Hfacts').
    pose proof (smatch_swf segs _ _ _ Hsm') as Hwf'.
    rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
    eapply (next_rel_core1 rho rho' S S'); [exact Hsm | exact Hi | discriminate | | exact Hag | | exact Hsm' | | | | | | | |].
    + cbn [exec]. cbn [interp_eff0 width_bytes]. rewrite Haddr.
      change (Z.to_nat 4) with 4%nat in Hrd. rewrite Hrd. reflexivity.
    + cbn. lia.
    + rewrite swf_set_pc. apply swf_set_freg; [exact Hwf'|]. apply mk_nanbox_below. exact Hbelow.
    + cbn [ss_pc set_pc set_freg c_pc fset with_fregs with_pc core_of]. unfold ms_pc in Hpc. rewrite Hpc. apply pc_plus'.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & Hr1 & _). eapply regs_match_same; [exact Hr1 | reflexivity | reflexivity].
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & Hfr1 & _). cbn [fst snd cfg_ms] in Hfr1.
      unfold set_pc. cbn [ss_fregs]. eapply (fregs_match_fset rho' S' ms); [exact Hwf' | exact Hfr1 | | reflexivity].
      apply mk_nanbox_sound. rewrite Hev. reflexivity.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & Hc1 & _). cbn. exact Hc1.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv1 & _). cbn. unfold resv_match in Hv1 |- *. cbn [ms_resv ms_of]. exact Hv1.
    + reflexivity.
    + reflexivity.
  -
    destruct (sym_load_sound_gen segs rho S tr ms md _ 8 true v S' Hsm Hae ltac:(lia) Hload) as [(Hlen & Hrd & _ & _) | HLP].
    { left. split; [exact Hlen|]. rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
      rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
      cbn [exec]. cbn [interp_eff0 width_bytes]. rewrite Haddr.
      change (Z.to_nat 8) with 8%nat in Hrd. rewrite Hrd. reflexivity. }
    right.
    destruct (load_post_proj _ _ _ _ _ _ _ _ _ _ HLP)
      as (bs & rho' & Hrd & Hag & Hnext & Hsm' & Hev & Hbelow & Hpc' & Hregs' & Hfregs' & Hfcsr' & Hresv' & Hfacts').
    pose proof (smatch_swf segs _ _ _ Hsm') as Hwf'.
    rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
    eapply (next_rel_core1 rho rho' S S'); [exact Hsm | exact Hi | discriminate | | exact Hag | | exact Hsm' | | | | | | | |].
    + cbn [exec]. cbn [interp_eff0 width_bytes]. rewrite Haddr.
      change (Z.to_nat 8) with 8%nat in Hrd. rewrite Hrd. reflexivity.
    + cbn. lia.
    + rewrite swf_set_pc. apply swf_set_freg; [exact Hwf'|]. exact Hbelow.
    + cbn [ss_pc set_pc set_freg c_pc fset with_fregs with_pc core_of]. unfold ms_pc in Hpc. rewrite Hpc. apply pc_plus'.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & Hr1 & _). eapply regs_match_same; [exact Hr1 | reflexivity | reflexivity].
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & Hfr1 & _). cbn [fst snd cfg_ms] in Hfr1.
      unfold set_pc. cbn [ss_fregs]. eapply (fregs_match_fset rho' S' ms); [exact Hwf' | exact Hfr1 | | reflexivity].
      rewrite Hev. cbn [ext_low]. apply sext_64_64.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & Hc1 & _). cbn. exact Hc1.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv1 & _). cbn. unfold resv_match in Hv1 |- *. cbn [ms_resv ms_of]. exact Hv1.
    + reflexivity.
    + reflexivity.
Qed.

Definition ffmt_k (fmt : ffmt) : Z := match fmt with FMT_S => 4 | FMT_D => 8 end.

Lemma case_fstore : ltac2:(tb__ "0|2|
S5S2dS28Q5A1M0G0S28QcA1S5S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS3bR9R8R7R6A4A2A3S0S4bS6A1SfRbA1S50S6A1A3S0S4bS5A1S81RcS7fS6cRcRaA2S7eR8A1A2Sb4RbA1S78RcR9A2A4S4dS5R7A2A3S9Vsegs;R7RdS4cG1S63R6S64R5R4A2A4A4S83Vsegs;ReS68R9S86S7ReA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fimm;Frs2;Frs1;Ffmt;FS;").
Proof using .
  intros S fmt rs1 rs2 imm S' rho tr ms md Hi Hresv Hst Hsm.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hkc : ffmt_k fmt = 1 \/ ffmt_k fmt = 2 \/ ffmt_k fmt = 4 \/ ffmt_k fmt = 8) by (destruct fmt; cbn; lia).
  assert (Hae : sv_below (ss_next S) (mk_addk (get_reg S rs1) (immI imm)) = true) by (apply mk_addk_below, get_reg_below; exact Hwf).
  assert (Hv : sv_below (ss_next S) (get_freg S rs2) = true) by (apply get_freg_below; exact Hwf).
  destruct (sym_store_sound segs S _ (ffmt_k fmt) _ S' rho tr ms md Hst Hsm0 Hae Hv Hkc) as (Hok & objs' & ES & Hwf' & Hpost).
  subst S'. cbn zeta in Hok, Hpost.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho (mk_addk (get_reg S rs1) (immI imm))).
  { rewrite (rget_match segs rho S tr ms md rs1 Hsm0). change (sext 64 imm) with (Z_to_bv 64 (immI imm)).
    rewrite <- mk_addk_sound. reflexivity. }
  assert (Hresv0 : ms_resv ms = None).
  { unfold resv_match in Hresvm. rewrite Hresv in Hresvm. destruct (ms_resv ms); [destruct Hresvm|reflexivity]. }
  assert (Hval : fget (core_of ms) rs2 = eval rho (get_freg S rs2)) by (eapply fget_match; exact Hsm0).
  set (a := eval rho (mk_addk (get_reg S rs1) (immI imm))) in *.
  set (bs := enc_bytes (Z.to_nat (ffmt_k fmt)) (eval rho (get_freg S rs2))) in *.
  set (m' := write_to_mem (ms_mem ms) a bs).
  set (ms1 := ms_of ms (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)) m').
  destruct (Hpost ms1 eq_refl eq_refl) as [Hroc1 Hmem1].
  eapply next_rel_same_rho with (ms' := ms1).
  - rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (FStore fmt rs1 rs2 imm) (core_of ms))
      with ((match fmt with
             | FMT_S => EStore 32 (rget (core_of ms) rs1 + sext 64 imm)%bv (low32 (fget (core_of ms) rs2))
             | FMT_D => EStore 64 (rget (core_of ms) rs1 + sext 64 imm)%bv (fget (core_of ms) rs2)
             end) (EDone (inval_resv (rget (core_of ms) rs1 + sext 64 imm)%bv
                        (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))))).
    rewrite Haddr, Hval.
    assert (Hinv : inval_resv a (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))
                   = with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)).
    { unfold inval_resv, with_pc, with_resv, core_of. cbn. rewrite Hresv0.
      change (ms_pc_val ms) with (ms_pc ms). rewrite Hpc, pc_plus'. reflexivity. }
    destruct fmt; cbn [interp_eff0 width_bytes].
    + change (Z.to_nat (ffmt_k FMT_S)) with 4%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ4 (eval rho (get_freg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (ffmt_k FMT_D)) with 8%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ8 (eval rho (get_freg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
  - cbn. lia.
  - unfold smatch. cbn [fst snd cfg_ms cfg_model set_pc set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    split; [rewrite swf_set_pc; exact Hwf' |].
    split; [reflexivity | split; [reflexivity | split; [exact Hhalt | split; [exact Hrom | split; [exact Hroc1|]]]]].
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|].
    split; [unfold resv_match; rewrite Hresv; cbn; rewrite Hresv0; exact I|].
    split; [exact Hmem1 | exact Hfacts].
Qed.

Lemma slice_get_frm_zero : ltac2:(tb__ "0|2|
S28Q20M0A1S87S29G0R1A2Z20A2S0S28Q40M1A1Sa8R2Z5Z3A3S2aG1Z0A2A3F_;Ff;").
Proof using .
  intros f Hf. unfold slice_get. pose proof (bv_unsigned_in_range _ f).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma slice_set_flags_bound : ltac2:(tb__ "0|2|
S28Q20M0A1S28Q40A1S87S29G0R2A2Z20M1A2S87S29G0Sa9R3Z0Z5R2A4A2G1A2F_;Fv;Ff;").
Proof using .
  intros f v Hf. unfold slice_set. pose proof (bv_unsigned_in_range _ f) as Rf. pose proof (bv_unsigned_in_range _ v) as Rv.
  rewrite Z.shiftl_0_r. change (Z.shiftl (Z.ones 5) 0) with (Z.ones 5).
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite Z.div_small by lia.
  rewrite Z.shiftl_0_l, Z.lor_0_l. rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  pose proof (Z.mod_pos_bound (bv_unsigned v) 32 ltac:(lia)).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sym_csr_not_illegal : ltac2:(tb__ "0|0|
S5S2eS28Q5A1S48S28QcA1S5S0S74S75R6R5R4R3R2A5S70R1A1A3S0S48S9dR4R3A2S51A3F_;FS';Fcsr;Fwrites;Frd;Fop;FS;").
Proof using .
  intros S op rd writes csr S' Hsym. unfold sym_csr in Hsym.
  destruct (ss_fcsr S); [|discriminate].
  unfold csr_write_illegal, csr_read_only.
  destruct ((bv_unsigned csr =? 2) && negb writes) eqn:E1.
  - apply andb_prop in E1 as [E1 _]. apply Z.eqb_eq in E1. rewrite E1. destruct writes; reflexivity.
  - destruct (bv_unsigned csr =? 1) eqn:E2; [|discriminate]. apply Z.eqb_eq in E2. rewrite E2. destruct writes; reflexivity.
Qed.

Lemma case_csr_gen : ltac2:(tb__ "0|4|
S5S2cS2eS28Q5A1S28Q40M0A1S48S28QcA1S8S4aS65A1M1S57S66S5S0S4bS2cA1S67Vsegs;S7RcA1A2S4dS2cRbA2A3S2S0S2cRcS2fA3A1S0S95S93S2aG0Z4A2M2RdS8fR5A1M3A3S48S95L_;S9dR9R8A2S9fG3A1Sa3RcRbRaR9R8S9cS2bG0S94G3A1G2A3G3A2A6X48x2A3S9Vsegs;R8RfS4cG1S63R7S64R6R5A2A4A4S0S74S75R10ReRdRbRaA5S70R5A1A3S83Vsegs;R11R6RaR9R8R7A7F_;F_;F_;F_;F_;FS';Fmd;Fms;Ftr;Frho;Fcsr;Fwrites;Foperand;Frd;Fop;Fi;FS;").
Proof using .
  intros S i op rd operand writes csr rho tr ms md S' Hi Hne Hex Hsm Hsym.
  rewrite (sym_csr_not_illegal _ _ _ _ _ _ Hsym) in Hex.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  unfold sym_csr in Hsym. destruct (ss_fcsr S) eqn:Hfrm; [|discriminate].
  pose proof (fcsr_frm0_bound _ _ _ _ _ Hsm Hfrm) as Hb.
  destruct ((bv_unsigned csr =? 2) && negb writes) eqn:E1.
  - apply andb_prop in E1 as [E1 E2]. apply Z.eqb_eq in E1. destruct writes; [discriminate|]. clear E2.
    injection Hsym as <-.
    eapply step_rd_sound; [exact Hsm | exact Hi | exact Hne | | eapply npc_eq; eauto | reflexivity |].
    + rewrite Hex. unfold exec_csr, csr_slice. rewrite E1. cbn [Z.eqb Pos.eqb].
      rewrite slice_get_frm_zero by exact Hb. reflexivity.
    + reflexivity.
  - destruct (bv_unsigned csr =? 1) eqn:E2; [|discriminate]. apply Z.eqb_eq in E2.
    cbn [fresh] in Hsym. injection Hsym as <-.
    change (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S) (ss_facts S) (Pos.succ (ss_next S)) (ss_lenient S))
      with (snd (fresh S)).
    change (SVar (ss_next S)) with (fst (fresh S)).
    eapply (havoc_reg_sound _ _ _ _ _ i rd
              (rset rd (slice_get (ms_fcsr ms) 0 5)
                 (if writes then with_fcsr (slice_set (ms_fcsr ms) 0 5
                      (match op with CSR_RW => operand | CSR_RS => bv_or (slice_get (ms_fcsr ms) 0 5) operand
                                   | CSR_RC => bv_and (slice_get (ms_fcsr ms) 0 5) (bv_not operand) end))
                      (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))
                  else with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))
              (slice_get (ms_fcsr ms) 0 5) Hsm Hi Hne).
    + rewrite Hex. unfold exec_csr, csr_slice. rewrite E2. reflexivity.
    + apply c_regs_rset. destruct writes; reflexivity.
    + unfold rset. destruct (is_x0 rd), writes; reflexivity.
    + unfold rset. destruct (is_x0 rd), writes; reflexivity.
    + unfold rset. destruct (is_x0 rd), writes; reflexivity.
    + exact Hfrm.
    + unfold rset. destruct (is_x0 rd), writes; cbn; try exact Hb; apply slice_set_flags_bound; exact Hb.
Qed.

Lemma case_csr : ltac2:(tb__ "0|3|
S5S2eS28Q5A1M0G0S28QcA1S8S4aS65A1M1S57S66S5S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS38R9R8R7R6A4A2A3S9Vsegs;R6RbS4cG1S63R5S64R4R3A2A4A4S0S74S75RcRbRaS2eS48Lop;RbS49S54Sa7R9A1A1M2G2X2ex3R8A5S70R3A1A3S83Vsegs;RdR4R8R7R6R5A7F_;F_;F_;FS';Fmd;Fms;Ftr;Frho;Fcsr;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm Hsym. eapply case_csr_gen; [exact Hi | discriminate | reflexivity | exact Hsm | exact Hsym].
Qed.

Lemma case_csri : ltac2:(tb__ "0|4|
S5S2eS28Q5M0A1M1G1S28QcA1S8S4aS65A1M2S57S66S5S0S4bS2cA1S67Vsegs;S7RaA1A2S4dS2cS39R9R8R7R6A4A2A3S9Vsegs;R6RbS4cG2S63R5S64R4R3A2A4A4S0S74S75RcRbRaS2eS48Lop;RbS49S54S8bS29G0R9A2Z0A2A1M3G3X2ex3R8A5S70R3A1A3S83Vsegs;RdR4R8R7R6R5A7F_;F_;F_;FS';Fmd;Fms;Ftr;Frho;Fcsr;Fuimm;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm Hsym. eapply case_csr_gen; [exact Hi | discriminate | reflexivity | exact Hsm | exact Hsym].
Qed.

Lemma mod_pow2_mono : ltac2:(tb__ "0|2|
S84S84S84S1S88Z0R2A2S88R2R1A2A2S0S84S8aS8aR4S89Z2M0R2A2A2S89G0R3A2M1A2S8aR4G1A2A3F_;Fb;Fa;Fx;").
Proof using .
  intros x a b H.
  rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
  - reflexivity.
  - exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma align_weaken : ltac2:(tb__ "0|2|
S84S84S84S1S88Z0M0R2A2S88R2R1A2A2S0S84S8aR4S89Z2M1R2A2A2G0A3S0S84S8aR5S89G1R4A2A2G0A3F_;F_;Fb;Fa;Fx;").
Proof using .
  intros x a b H Hb. rewrite <- (mod_pow2_mono x a b H). rewrite Hb. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.

Lemma addr_aligned_sound : ltac2:(tb__ "0|1|
S8S4aS13A1S6S84Sb7S13S22R4A1R3A3S0S48S6fR4R3R2A3S49A3S1S88Z0M0R3A2S0S84S8aS29Q40SeR6R4A2A2S89Z2R3A2A2G0A3A2F_;F_;Fa;Fe;Ffacts;Frho;").
Proof using .
  intros rho facts e a Hf H. unfold addr_aligned in H.
  apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [exact H1|].
  destruct e; try discriminate.
  - cbn. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.eqb_eq in H3. exact H3.
  - cbn. apply Z.leb_le in H3.
    pose proof (align_of_sound rho facts i Hf) as [Ha0 Hal].
    eapply align_weaken; [|exact Hal]. lia.
  - destruct op; try discriminate. destruct e1; try discriminate. destruct e2; try discriminate.
    apply andb_prop in H3 as [H3 H4]. apply Z.leb_le in H3. apply Z.eqb_eq in H4.
    pose proof (align_of_sound rho facts i Hf) as [Ha0 Hal].
    cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    rewrite (congr_add (bv_unsigned (rw rho i)) z a); [| lia | eapply align_weaken; [|exact Hal]; lia].
    rewrite <- (mod_pow2_mono z a 64) by lia. exact H4.
Qed.

Lemma amo_aligned_of : ltac2:(tb__ "0|0|
S8S5S52S4aS65A1S63A2S30S6S9Vsegs;R5R4R3A4S0S48S6fSbR5A1R2S71R3A1A3S49A3S0S48Sa2R4SeR7R3A2A2S49A3F_;F_;Fae;Fwd;Fw;FS;Frho;").
Proof using .
  intros rho S w wd ae Hsm H. pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  destruct (addr_aligned_sound rho (ss_facts S) ae (amo_log wd) Hf H) as [_ Hm].
  unfold amo_aligned, amo_bytes. apply Z.eqb_eq. destruct wd; cbn [amo_log] in Hm.
  - change 4 with (2 ^ 2). exact Hm.
  - change 8 with (2 ^ 3). exact Hm.
Qed.

Lemma swf_set_resv : ltac2:(tb__ "0|0|
S5S6S0S48SaR2A1S49A3S0S48S16SdR3A1R2A2S49A3S0S48SaS73R4S4dS6R3A2A2A1S49A3F_;F_;Fe;FS;").
Proof using .
  intros S e Hwf He. pose proof Hwf as W. unfold swf in W |- *.
  unfold set_resv. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  repeat (apply andb_prop in W; destruct W as [W ?]).
  repeat (apply andb_true_intro; split); try assumption.
Qed.

Lemma swf_set_resv_none : ltac2:(tb__ "0|0|
S5S0S48SaR1A1S49A3S0S48SaS73R2S50S6A1A2A1S49A3F_;FS;").
Proof using .
  intros S Hwf. pose proof Hwf as W. unfold swf in W |- *.
  unfold set_resv. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  repeat (apply andb_prop in W; destruct W as [W ?]).
  repeat (apply andb_true_intro; split); try assumption. reflexivity.
Qed.

Lemma amo_k_cases : ltac2:(tb__ "0|1|
S30S4S0S84S76R1A1M0Z1A3S4S0S84G0Z2A3S4S0S84G0Z4A3S0S84G0Z8A3A2A2A2Fwd;").
Proof using . destruct wd; cbn; lia. Qed.

Lemma case_lr : ltac2:(tb__ "0|2|
S5S30S48S48S28Q5A1M0G0S6S5S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RcA1A2S4dS2cS43RbRaR9R8R7A5A2A3S0S48S6fSbRdA1S6cRdR8A2S71RcA1A3S49A3S0S79S7aVsegs;ReS6cReR9A2S76RdA1S49A5S7bR8R7A2A3S9Vsegs;R7RfS4cG1S63R6S64R5R4A2A4A4Sb5Vsegs;R10S68S73S6bR9RcRaA3S4dS6S6cR10RbA2A2A2S86S7R10A1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fv;Frs1;Frd;Frl;Faq;Fwd;FS;").
Proof using .
  intros S wd aq rl rd rs1 v S' rho tr ms md Hi Hal Hload Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  assert (Hae : sv_below (ss_next S) (get_reg S rs1) = true) by (apply get_reg_below; exact Hwf).
  assert (Hrom : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & Hrom & _); exact Hrom).
  pose proof Hsm as Hsm0.
  destruct Hsm0 as (_ & Hpc & _ & _ & _ & _ & _ & _ & _ & _ & _). cbn [fst snd cfg_ms cfg_model] in Hpc.
  pose proof (amo_aligned_of rho S _ wd _ Hsm Hal) as Hamo.
  rewrite <- (rget_match segs rho S tr ms md rs1 Hsm) in Hamo.
  destruct (sym_load_sound_gen segs rho S tr ms md _ (amo_k wd) true v S' Hsm Hae (amo_k_cases wd) Hload) as [(Hlen & Hrd & _ & _) | HLP].
  { left. split; [exact Hlen|]. rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
    rewrite <- (rget_match segs rho S tr ms md rs1 Hsm) in Hrd.
    rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    destruct wd; cbn [exec]; rewrite Hamo; cbn [negb amo_k interp_eff0 width_bytes].
    - change (Z.to_nat (amo_k AW)) with 4%nat in Hrd. rewrite Hrd. reflexivity.
    - change (Z.to_nat (amo_k AD)) with 8%nat in Hrd. rewrite Hrd. reflexivity. }
  right.
  destruct (load_post_proj _ _ _ _ _ _ _ _ _ _ HLP)
    as (bs & rho' & Hrd & Hag & Hnext & Hsm' & Hev & Hbelow & Hpc' & Hregs' & Hfregs' & Hfcsr' & Hresv' & Hfacts').
  pose proof (smatch_swf segs _ _ _ Hsm') as Hwf'.
  rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
  rewrite <- (rget_match segs rho S tr ms md rs1 Hsm) in Hrd.
  assert (Hbelow2 : sv_below (ss_next S') (get_reg S rs1) = true).
  { eapply sv_below_mono; [exact Hnext | exact Hae]. }
  destruct wd.
  - eapply (next_rel_core1 rho rho' S S'); [exact Hsm | exact Hi | discriminate | | exact Hag | | exact Hsm' | | | | | | | |].
    + cbn [exec]. rewrite Hamo. cbn [negb amo_k interp_eff0 width_bytes].
      change (Z.to_nat (amo_k AW)) with 4%nat in Hrd. rewrite Hrd. reflexivity.
    + cbn. rewrite ss_next_set_reg. lia.
    + rewrite swf_set_pc. apply swf_set_resv; [apply swf_set_reg; assumption|]. rewrite ss_next_set_reg. exact Hbelow2.
    + cbn [ss_pc set_pc set_resv].
      unfold rset, with_resv, with_regs, with_pc, core_of; destruct (is_x0 rd); cbn [c_pc]; unfold ms_pc in Hpc; rewrite Hpc; apply pc_plus'.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & Hr1 & _). cbn [fst snd cfg_ms] in Hr1.
      eapply (regs_match_same rho' (set_reg S' rd v) _ (ms_of ms _ (ms_mem ms))); [| reflexivity | cbn [set_pc set_resv ss_regs]; reflexivity].
      eapply (regs_match_rset_gen rho' S' _ ms); [exact Hwf' | exact Hr1 | |].
      * rewrite Hev. cbn [ext_low amo_k]. reflexivity.
      * cbn [ms_regs ms_of]. unfold rset, with_resv, with_regs, with_pc, core_of; destruct (is_x0 rd); reflexivity.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & Hfr1 & _). cbn [fst snd cfg_ms] in Hfr1.
      eapply fregs_match_same; [exact Hfr1 | | ]; [unfold rset; destruct (is_x0 rd); reflexivity|].
      cbn. rewrite ss_fregs_set_reg. reflexivity.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & Hc1 & _). cbn [fst snd cfg_ms] in Hc1.
      cbn [ss_fcsr set_pc set_resv]. rewrite ss_fcsr_set_reg.
      unfold fcsr_match in Hc1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hc1.
    + cbn [ss_resv set_pc set_resv]. unfold resv_match. unfold rset; destruct (is_x0 rd); cbn;
        rewrite (rget_match segs rho S tr ms md rs1 Hsm); rewrite (eval_agree _ _ _ _ Hag Hae); reflexivity.
    + cbn. rewrite ss_objs_set_reg. reflexivity.
    + cbn. rewrite ss_facts_set_reg. reflexivity.
  - eapply (next_rel_core1 rho rho' S S'); [exact Hsm | exact Hi | discriminate | | exact Hag | | exact Hsm' | | | | | | | |].
    + cbn [exec]. rewrite Hamo. cbn [negb amo_k interp_eff0 width_bytes].
      change (Z.to_nat (amo_k AD)) with 8%nat in Hrd. rewrite Hrd. reflexivity.
    + cbn. rewrite ss_next_set_reg. lia.
    + rewrite swf_set_pc. apply swf_set_resv; [apply swf_set_reg; assumption|]. rewrite ss_next_set_reg. exact Hbelow2.
    + cbn [ss_pc set_pc set_resv].
      unfold rset, with_resv, with_regs, with_pc, core_of; destruct (is_x0 rd); cbn [c_pc]; unfold ms_pc in Hpc; rewrite Hpc; apply pc_plus'.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & Hr1 & _). cbn [fst snd cfg_ms] in Hr1.
      eapply (regs_match_same rho' (set_reg S' rd v) _ (ms_of ms _ (ms_mem ms))); [| reflexivity | cbn [set_pc set_resv ss_regs]; reflexivity].
      eapply (regs_match_rset_gen rho' S' _ ms); [exact Hwf' | exact Hr1 | |].
      * rewrite Hev. cbn [ext_low amo_k]. apply sext_64_64.
      * cbn [ms_regs ms_of]. unfold rset, with_resv, with_regs, with_pc, core_of; destruct (is_x0 rd); reflexivity.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & Hfr1 & _). cbn [fst snd cfg_ms] in Hfr1.
      eapply fregs_match_same; [exact Hfr1 | | ]; [unfold rset; destruct (is_x0 rd); reflexivity|].
      cbn. rewrite ss_fregs_set_reg. reflexivity.
    + destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & Hc1 & _). cbn [fst snd cfg_ms] in Hc1.
      cbn [ss_fcsr set_pc set_resv]. rewrite ss_fcsr_set_reg.
      unfold fcsr_match in Hc1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hc1.
    + cbn [ss_resv set_pc set_resv]. unfold resv_match. unfold rset; destruct (is_x0 rd); cbn;
        rewrite (rget_match segs rho S tr ms md rs1 Hsm); rewrite (eval_agree _ _ _ _ Hag Hae); reflexivity.
    + cbn. rewrite ss_objs_set_reg. reflexivity.
    + cbn. rewrite ss_facts_set_reg. reflexivity.
Qed.

Lemma case_sc_fail : ltac2:(tb__ "0|2|
S5S30S48S48S28Q5A1M0G0G0S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RbA1A2S4dS2cS35RaR9R8R7R6R5A6A2A3S0S48S6fSbRcA1S6cRcR7A2S71RbA1A3S49A3S0S4bS6A1SfRdA1S50S6A1A3S9Vsegs;R7ReS4cG1S63R6S64R5R4A2A4A4S83Vsegs;RfS68S6bRfRbS17Z1A1A3S86S7RfA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Frl;Faq;Fwd;FS;").
Proof using .
  intros S wd aq rl rd rs1 rs2 rho tr ms md Hi Hal Hresv Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof Hsm as Hsm0.
  destruct Hsm0 as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _). cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hresv0 : ms_resv ms = None).
  { unfold resv_match in Hv1. rewrite Hresv in Hv1. destruct (ms_resv ms); [destruct Hv1|reflexivity]. }
  pose proof (amo_aligned_of rho S _ wd _ Hsm Hal) as Hamo.
  rewrite <- (rget_match segs rho S tr ms md rs1 Hsm) in Hamo.
  eapply (next_rel_core1 rho rho S S); [exact Hsm | exact Hi | discriminate | | apply agree_below_refl | | exact Hsm | | | | | | | |].
  - cbn [exec]. rewrite Hamo. cbn [negb c_resv core_of]. rewrite Hresv0.
    destruct wd; reflexivity.
  - cbn. rewrite ss_next_set_reg. lia.
  - rewrite swf_set_pc. apply swf_set_reg; [exact Hwf | reflexivity].
  - cbn [ss_pc set_pc].
    unfold rset, with_resv, with_regs, with_pc, core_of; destruct (is_x0 rd); cbn [c_pc]; unfold ms_pc in Hpc; rewrite Hpc; apply pc_plus'.
  - eapply (regs_match_same rho (set_reg S rd (SLit 1)) _ (ms_of ms _ (ms_mem ms))); [| reflexivity | cbn [set_pc ss_regs]; reflexivity].
    eapply (regs_match_rset_gen rho S _ ms); [exact Hwf | exact Hr1 | reflexivity |].
    cbn [ms_regs ms_of]. unfold rset, with_resv, with_regs, with_pc, core_of; destruct (is_x0 rd); reflexivity.
  - eapply fregs_match_same; [exact Hfr1 | | ]; [unfold rset; destruct (is_x0 rd); reflexivity|].
    cbn. rewrite ss_fregs_set_reg. reflexivity.
  - cbn [ss_fcsr set_pc]. rewrite ss_fcsr_set_reg.
    unfold fcsr_match in Hc1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hc1.
  - cbn [ss_resv set_pc]. rewrite ss_resv_set_reg, Hresv. unfold resv_match. unfold rset; destruct (is_x0 rd); cbn; exact I.
  - cbn. rewrite ss_objs_set_reg. reflexivity.
  - cbn. rewrite ss_facts_set_reg. reflexivity.
Qed.

Lemma case_sc_ok : ltac2:(tb__ "0|2|
S5S30S48S48S28Q5A1M0G0G0S6S5S8S4aS65A1M1S57S66S0S4bS2cA1S67Vsegs;S7RdA1A2S4dS2cS35RcRbRaR9R8R7A6A2A3S0S48S6fSbReA1S6cReR9A2S71RdA1A3S49A3S0S4bS6A1SfRfA1S4dS6R8A2A3S0S48S27R9S6cR10RbA2A2S49A3S0S4bS5A1S81S73R11S50S6A1A2S6cR11RcA2S76R10A1S6cR11RbA2A4S4dS5R9A2A3S9Vsegs;R9R12S4cG1S63R8S64R7R6A2A4A4S83Vsegs;R13S68S6bRbRfS17Z0A1A3S86S7R13A1Z4A2A2RaR9R8R7A7F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fe;Frs2;Frs1;Frd;Frl;Faq;Fwd;FS;").
Proof using .
  intros S wd aq rl rd rs1 rs2 e S' rho tr ms md Hi Hal Hresv Heq Hst Hsm.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  apply sv_eqb_sound in Heq. subst e.

  assert (Hok : match c_resv (core_of ms) with
                | Some r => Z.eqb (bv_unsigned r) (bv_unsigned (rget (core_of ms) rs1))
                | None => false end = true).
  { unfold resv_match in Hresvm. rewrite Hresv in Hresvm. cbn [c_resv core_of].
    destruct (ms_resv ms) as [r|]; [|destruct Hresvm]. apply Z.eqb_eq. rewrite Hresvm.
    rewrite (rget_match segs rho S tr ms md rs1 Hsm0). reflexivity. }
  pose proof (amo_aligned_of rho S _ wd _ Hsm0 Hal) as Hamo.
  rewrite <- (rget_match segs rho S tr ms md rs1 Hsm0) in Hamo.

  set (msr := ms_of ms (with_resv None (core_of ms)) (ms_mem ms)).
  assert (Hsmr : smatch segs rho (set_resv S None) (tr, mkCfg msr md)).
  { unfold smatch. cbn [fst snd cfg_ms cfg_model set_resv ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    split; [apply swf_set_resv_none; exact Hwf|].
    split; [exact Hpc|]. split; [reflexivity|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact I|].
    split; [| exact Hfacts]. apply (mem_match_same_mem segs rho (ss_objs S) ms); [reflexivity|reflexivity|exact Hmem]. }
  assert (Hae : sv_below (ss_next (set_resv S None)) (get_reg S rs1) = true) by (cbn [ss_next set_resv]; apply get_reg_below; exact Hwf).
  assert (Hv : sv_below (ss_next (set_resv S None)) (get_reg S rs2) = true) by (cbn [ss_next set_resv]; apply get_reg_below; exact Hwf).
  destruct (sym_store_sound segs (set_resv S None) _ (amo_k wd) _ S' rho tr msr md Hst Hsmr Hae Hv (amo_k_cases wd)) as (Hsok & objs' & ES & Hwf' & Hpost).
  subst S'. cbn zeta in Hsok, Hpost. cbn [ms_mem ms_of msr] in Hsok, Hpost.
  set (a := eval rho (get_reg S rs1)) in *.
  set (bs := enc_bytes (Z.to_nat (amo_k wd)) (eval rho (get_reg S rs2))) in *.
  set (m' := write_to_mem (ms_mem ms) a bs).
  set (c1 := rset rd w0 (with_resv None (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)))).
  set (ms1 := ms_of ms c1 m').
  set (ms0 := ms_of ms (with_resv None (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms))) m').
  destruct (Hpost ms0 eq_refl eq_refl) as [Hroc1 Hmem1].
  eapply next_rel_same_rho with (ms' := ms1).
  - rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    cbn [exec]. rewrite Hamo. cbn [negb]. rewrite Hok.
    rewrite (rget_match segs rho S tr ms md rs1 Hsm0). rewrite (rget_match segs rho S tr ms md rs2 Hsm0). fold a.
    assert (Hnpc : (c_pc (core_of ms) + Z_to_bv 64 4)%bv = Z_to_bv 64 (ss_pc S + 4)).
    { cbn [c_pc core_of]. change (ms_pc_val ms) with (ms_pc ms). rewrite Hpc. apply pc_plus'. }
    destruct wd; cbn [interp_eff0 width_bytes amo_k] in Hsok |- *.
    + change (Z.to_nat 4) with 4%nat in Hsok. rewrite Hsok, Hnpc.
      pose proof (store_bytes_enc SZ4 (eval rho (get_reg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat 8) with 8%nat in Hsok. rewrite Hsok, Hnpc.
      pose proof (store_bytes_enc SZ8 (eval rho (get_reg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
  - cbn. rewrite ss_next_set_reg. cbn. lia.
  - set (Sst := set_objs (set_resv S None) objs').
    assert (Hsm1 : smatch segs rho (set_pc Sst (ss_pc S + 4)) (tr, mkCfg ms0 md)).
    { unfold smatch. cbn [fst snd cfg_ms cfg_model set_pc set_objs set_resv ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next Sst].
      split; [rewrite swf_set_pc; exact Hwf' |].
      split; [reflexivity | split; [reflexivity | split; [exact Hhalt | split; [exact Hrom | split; [exact Hroc1|]]]]].
      split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|].
      split; [exact I|]. split; [exact Hmem1 | exact Hfacts]. }
    pose proof (smatch_rd_pc segs rho (set_pc Sst (ss_pc S + 4)) tr ms0 md rd (SLit 0) w0 (ss_pc S + 4) Hsm1 eq_refl eq_refl) as Hsm2.
    assert (Ems : ms_of ms0 (rset rd w0 (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms0))) (ms_mem ms0) = ms1).
    { unfold ms1, ms0, c1, ms_of, rset, with_resv, with_pc, with_regs, core_of. destruct (is_x0 rd); reflexivity. }
    rewrite Ems in Hsm2.
    assert (ES : set_pc (set_reg (set_pc Sst (ss_pc S + 4)) rd (SLit 0)) (ss_pc S + 4) = set_pc (set_reg Sst rd (SLit 0)) (ss_pc S + 4)).
    { unfold set_pc, set_reg. destruct (regZ rd =? 0); reflexivity. }
    rewrite ES in Hsm2. exact Hsm2.
Qed.

End F.
