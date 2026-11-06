(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "pair"; "true"; "Some"; "None"; "nat"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "ss_next"; "ss_lenient"; "sv"; "smatch"; "agree_below"; "ss_pc"; "ss_facts"; "sobj"; "tfact"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "machine_result"; "step"; "ms_svc_pending"; "MachineFault"; "MachineOk"; "MachineUnmodeled"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple1"; "model_idle"; "tcons"; "wstep"; "ok_src"; "triple"; "w_cfg"; "w_tr"; "ok_tgt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "step_out"; "sym_run"; "get_reg"; "stop_reason"; "sym_step"; "set_reg"; "LROk"; "instr_at"; "load_res"; "set_pc"; "lf_state"; "load_arr"; "mk_op_f"; "mk_opw_f"; "sym_load"; "sym_store"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkCfg"; "config"; "cfg_model"; "SError"; "sstep"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.R"; "ok_frame"; "jpred"; "SP"; "SPJ"; "ok_fault"; "stableJ"; "LQ"; "LQJ"; "ok_frameJ"; "liftK"; "ok_faultJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "aluop"; "Op"; "Op32"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "step_rel"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section R.
Variable segs : list Segment.

Lemma case_op_f : ltac2:(tb__ "0|2|
S10S57S48Q5A1M0G0G0S11S6S23A1M1S1bS22S0S8S56A1S36Vsegs;S17R9A1A2SbS56S58R8R7R6R5A4A2A3S15Vsegs;R5RaS9G1S40R4S3fR3R2A2A4A4S54Vsegs;RbS38S34RbR9S3bS18RbA1RaS31RbR8A2S31RbR7A2A4A3S5aS17RbA1Z4A2A2R6R5R4R3A7F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | |].
  - apply mk_op_f_below; apply get_reg_below; eapply smatch_swf; eassumption.
  - rewrite (mk_op_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- !(rget_match segs rho S tr ms md _ Hsm). reflexivity.
Qed.

Lemma case_op32_f : ltac2:(tb__ "0|2|
S10S57S48Q5A1M0G0G0S11S6S23A1M1S1bS22S0S8S56A1S36Vsegs;S17R9A1A2SbS56S59R8R7R6R5A4A2A3S15Vsegs;R5RaS9G1S40R4S3fR3R2A2A4A4S54Vsegs;RbS38S34RbR9S3cS18RbA1RaS31RbR8A2S31RbR7A2A4A3S5aS17RbA1Z4A2A2R6R5R4R3A7F_;F_;Fmd;Fms;Ftr;Frho;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros * Hi Hsm. eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | |].
  - apply mk_opw_f_below; apply get_reg_below; eapply smatch_swf; eassumption.
  - rewrite (mk_opw_f_sound rho) by (eapply smatch_facts; eauto). rewrite <- !(rget_match segs rho S tr ms md _ Hsm). reflexivity.
Qed.

Theorem sym_step_sound : ltac2:(tb__ "0|1|
S10S11S6S23A1M0S1bS22S15Vsegs;R4R5S9G0S40R3S3fR2R1A2A4A4S2fOLx;S33Vsegs;R6A2S10S5bVsegs;R7R1R6R5R4R3A7LS';S10S10S2S54Vsegs;R8R2R7R6R5R4A7S54Vsegs;R8R1R7R6R5R4A7A2LS2;LS1;S32S3Lr;X2fx3F_;Fmd;Fms;Ftr;Frho;FS;").
Proof using .
  intros S rho tr ms md Hsm. unfold sym_step.
  destruct (instr_at segs (ss_pc S)) as [i|] eqn:Hi; [|exact I].
  destruct i; try exact I.
  - apply step_rel_of_next. eapply case_lui; eauto.
  - apply step_rel_of_next. eapply case_auipc; eauto.
  - apply step_rel_of_next. eapply case_jal; eauto.
  - destruct (mk_addk (get_reg S rs1) (immI imm)) eqn:Ht; try exact I.
    apply step_rel_of_next. eapply case_jalr; eauto.
  - pose proof (case_branch segs S c rs1 rs2 imm rho tr ms md Hi Hsm) as B. cbn zeta in B.
    destruct (decide_branch S c (get_reg S rs1) (get_reg S rs2)); try (apply step_rel_of_next; exact B).
    destruct B as [[_ B]|[_ B]]; [left|right]; exact B.
  - destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) (msz sz) signed) as [v S'|] eqn:Hl; [|exact I].
    eapply case_load; eauto.
  - destruct (ss_resv S) eqn:Hr; [exact I|].
    destruct (sym_store S (mk_addk (get_reg S rs1) (immI imm)) (msz sz) (get_reg S rs2)) as [S'|] eqn:Hs; [|exact I].
    apply step_rel_of_next. eapply case_store; eauto.
  - apply step_rel_of_next. eapply case_opimm; eauto.
  - apply step_rel_of_next. eapply case_shiftimm; eauto.
  - apply step_rel_of_next. eapply case_op_f; eauto.
  - apply step_rel_of_next. eapply case_opimm32; eauto.
  - apply step_rel_of_next. eapply case_shiftimm32; eauto.
  - apply step_rel_of_next. eapply case_op32_f; eauto.
  - apply step_rel_of_next. eapply case_fence; eauto.
  - apply step_rel_of_next. eapply case_fencei; eauto.
  - apply step_rel_of_next. eapply case_mul; eauto.
  - apply step_rel_of_next. eapply case_mul32; eauto.
  -   destruct (addr_aligned (ss_facts S) (get_reg S rs1) (amo_log w)) eqn:Hal; [|exact I]. cbn [negb].
    destruct (sym_load segs S (get_reg S rs1) (amo_k w) true) as [v S'|] eqn:Hl; [|exact I].
    eapply case_lr; eauto.
  -   destruct (addr_aligned (ss_facts S) (get_reg S rs1) (amo_log w)) eqn:Hal; [|exact I]. cbn [negb].
    destruct (ss_resv S) as [e|] eqn:Hr.
    + destruct (sv_eqb e (get_reg S rs1)) eqn:Heq; [|exact I].
      destruct (sym_store (set_resv S None) (get_reg S rs1) (amo_k w) (get_reg S rs2)) as [S'|] eqn:Hs; [|exact I].
      apply step_rel_of_next. eapply case_sc_ok; eauto.
    + apply step_rel_of_next. eapply case_sc_fail; eauto.
  -   destruct (sym_csr S op rd (match op with CSR_RW => true | _ => negb (is_x0 rs1) end) csr) as [S'| |] eqn:Hc;
      [apply step_rel_of_next; eapply case_csr; eauto | | exact I].
    exfalso. unfold sym_csr in Hc. destruct (ss_fcsr S); [|discriminate].
    destruct ((bv_unsigned csr =? 2) && _)%bool; [discriminate|]. destruct (bv_unsigned csr =? 1); discriminate.
  -   destruct (sym_csr S op rd (match op with CSR_RW => true | _ => negb (bv_unsigned uimm =? 0) end) csr) as [S'| |] eqn:Hc;
      [apply step_rel_of_next; eapply case_csri; eauto | | exact I].
    exfalso. unfold sym_csr in Hc. destruct (ss_fcsr S); [|discriminate].
    destruct ((bv_unsigned csr =? 2) && _)%bool; [discriminate|]. destruct (bv_unsigned csr =? 1); discriminate.
  -   destruct fmt.
    + destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) 4 false) as [v S'|] eqn:Hl; [|exact I].
      exact (case_fload segs S FMT_S rd rs1 imm v S' rho tr ms md Hi Hl Hsm).
    + destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) 8 true) as [v S'|] eqn:Hl; [|exact I].
      exact (case_fload segs S FMT_D rd rs1 imm v S' rho tr ms md Hi Hl Hsm).
  -   destruct (ss_resv S) eqn:Hr; [exact I|].
    destruct (sym_store S (mk_addk (get_reg S rs1) (immI imm)) (match fmt with FMT_S => 4 | FMT_D => 8 end) (get_freg S rs2)) as [S'|] eqn:Hs; [|exact I].
    apply step_rel_of_next. eapply (case_fstore segs S fmt); eauto.
  -   destruct (rm_ok S rm) eqn:Hok; [|exact I]. unfold havoc_freg. cbn [fresh].
    pose proof (case_fma segs S op fmt rd rs1 rs2 rs3 rm rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
  -   destruct (rm_ok S rm) eqn:Hok; [|exact I].
    pose proof (case_fari segs S op fmt rd rs1 rs2 rm rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
  -   destruct (rm_ok S rm) eqn:Hok; [|exact I].
    pose proof (case_fsqrt segs S fmt rd rs1 rm rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
  -   destruct (frm0b S) eqn:Hok; [|exact I].
    pose proof (case_fsgnj segs S op fmt rd rs1 rs2 rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
  -   destruct (frm0b S) eqn:Hok; [|exact I].
    pose proof (case_fminmax segs S op fmt rd rs1 rs2 rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
  -   destruct (frm0b S) eqn:Hok; [|exact I].
    pose proof (case_fcmp_b segs S op fmt rd rs1 rs2 rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
  -   destruct (rm_ok S rm) eqn:Hok; [|exact I]. cbn [negb].
    destruct (fcvt_fty dst && (fcvt_fty src || fcvt_ity src))%bool eqn:Hf.
    + pose proof (case_fcvt_f segs S dst src rd rs1 rm rho tr ms md Hi Hsm Hok Hf) as C. apply step_rel_of_next. exact C.
    + destruct (fcvt_ity dst && fcvt_fty src)%bool eqn:Hg; [|exact I].
      pose proof (case_fcvt_i segs S dst src rd rs1 rm rho tr ms md Hi Hsm Hok Hg) as C. apply step_rel_of_next. exact C.
  -   pose proof (case_fmv segs S dir fmt rd rs1 rho tr ms md Hi Hsm) as C.
    destruct dir, fmt; apply step_rel_of_next; exact C.
  -   destruct (frm0b S) eqn:Hok; [|exact I].
    pose proof (case_fclass segs S fmt rd rs1 rho tr ms md Hi Hsm Hok) as C. apply step_rel_of_next. exact C.
Qed.

Lemma wstep_of_step : ltac2:(tb__ "0|2|
S6S23A1M0S1bS22S1bS26R2A1S0S8S48Q40A1M1A1S1eR4A1ScG1A1A3S0S1cS1bA1S1dVsegs;R5A2S20S1bR3A2A3S28Vsegs;S9G0S40R7S3fR6R5A2A4S9G0S40R7S3fR4R5A2A4A3F_;F_;F_;Fms';Fmd;Fms;Ftr;").
Proof using .
  intros tr ms md ms' [Hh Hl] Hp Hs. exists []. split; [|cbn; rewrite app_nil_r; reflexivity].
  cbn. apply sstep_cfg_instr; [assumption | assumption |].
  rewrite (mi_account_step_lazy_nil segs ms md Hl), Hs. reflexivity.
Qed.

Lemma wstep_step_inv : ltac2:(tb__ "0|2|
S6S23A1M0S1bS22S1bS24S26R3A1S0S8S48Q40A1M1A1S1eR5A1ScG1A1A3S0S1cS1bA1S1dVsegs;R6A2S20S1bR4A2A3S28Vsegs;S9G0S40R8S3fR7R6A2A4R4A3S0S24R5S9G0S40R9S3fR6R7A2A4A3F_;F_;F_;F_;Fw';Fms';Fmd;Fms;Ftr;").
Proof using .
  intros tr ms md ms' [tr' c'] [Hh Hl] Hp Hs Hw. destruct Hw as [evs [Hst Heq]]. cbn in Hst, Heq.
  inversion Hst; subst; try congruence.
  match goal with H : mi_account_step segs ms md = MachineOk ?x |- _ =>
    rewrite (mi_account_step_lazy_nil segs ms md Hl), Hs in H; inversion H; subst end.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma wstep_fault_none : ltac2:(tb__ "0|2|
S6S23A1M0S1bS22S24S26R2A1S0S8S48Q40A1M1A1S1eR4A1ScG1A1A3S0S1cS1bA1S1dVsegs;R5A2S1fS1bA1A3S5S28Vsegs;S9G0S40R7S3fR6R5A2A4R4A3A1F_;F_;F_;Fw';Fmd;Fms;Ftr;").
Proof using .
  intros tr ms md [tr' c'] [Hh Hl] Hp Hs [evs [Hst Heq]]. cbn in Hst.
  inversion Hst; subst; try congruence.
  match goal with H : mi_account_step segs ms md = MachineOk ?x |- _ =>
    rewrite (mi_account_step_lazy_nil segs ms md Hl), Hs in H; inversion H end.
Qed.

Lemma sstep_error_step : ltac2:(tb__ "0|3|
S1bS22S6S23A1S26R2A1S0S8S48Q40A1M0A1S1eR4A1ScG0A1A3S43Vsegs;S3fR5R4A2R3S42A4S2S0S1cS1bA1M1S1dVsegs;R6A2M2S1fS1bA1A3S0G1G2S21S1bA1A3A2F_;F_;F_;Fevs;Fmd;Fms;").
Proof using .
  intros ms md evs [Hh Hl] Hp Hst. inversion Hst; subst; try congruence;
  match goal with H : mi_account_step segs ms md = ?x |- _ =>
    rewrite (mi_account_step_lazy_nil segs ms md Hl) in H;
    destruct (RiscvSemantics.step segs ms); try discriminate; auto end.
Qed.

Definition ok_frame (ok : world -> Prop) (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|2|
S6S23A1M0S1bS22S1bVK;R4R2A2S26R3A1S0S8S48Q40A1M1A1S1eR5A1ScG1A1A3S0S1cS1bA1S1dVsegs;R6A2S20S1bR4A2A3Vok;S9G0S40R8S3fR7R6A2A4A1F_;F_;F_;F_;Fms';Fmd;Fms;Ftr;").

Definition ok_fault (ok : world -> Prop) (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|2|
S6S23A1M0S1bS22VK;R3R1A2S26R2A1S0S8S48Q40A1M1A1S1eR4A1ScG1A1A3S0S1cS1bA1S1dVsegs;R5A2S1fS1bA1A3Vok;S9G0S40R7S3fR6R5A2A4A1F_;F_;F_;F_;Fmd;Fms;Ftr;").

Definition jpred : Type := ltac2:(tb__ "0|0|
S11S6S23A1S22OF_;F_;F_;").

Definition liftK (K : list event -> Model -> Prop) : jpred := fun _ tr md => K tr md.

Definition ok_frameJ (ok : world -> Prop) (J : jpred) : Prop := ltac2:(tb__ "0|2|
S11S6S23A1M0S1bS22S1bVJ;R5R4R2A3S26R3A1S0S8S48Q40A1M1A1S1eR5A1ScG1A1A3S0S1cS1bA1S1dVsegs;R6A2S20S1bR4A2A3Vok;S9G0S40R8S3fR7R6A2A4A1F_;F_;F_;F_;Fms';Fmd;Fms;Ftr;Frho;").

Definition ok_faultJ (ok : world -> Prop) (J : jpred) : Prop := ltac2:(tb__ "0|2|
S11S6S23A1M0S1bS22VJ;R4R3R1A3S26R2A1S0S8S48Q40A1M1A1S1eR4A1ScG1A1A3S0S1cS1bA1S1dVsegs;R5A2S1fS1bA1A3Vok;S9G0S40R7S3fR6R5A2A4A1F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;").

Lemma ok_frame_liftK : ltac2:(tb__ "0|0|
S24OF_;S6S23A1S22OF_;F_;S49R2R1A2S51R3S52R2A1A2F_;FK;Fok;").
Proof using . intros ok K H rho tr ms md ms' Hk. exact (H tr ms md ms' Hk). Qed.

Lemma ok_fault_liftK : ltac2:(tb__ "0|0|
S24OF_;S6S23A1S22OF_;F_;S4dR2R1A2S53R3S52R2A1A2F_;FK;Fok;").
Proof using . intros ok K H rho tr ms md Hk. exact (H tr ms md Hk). Qed.

Definition stableJ (n : positive) (J : jpred) : Prop := ltac2:(tb__ "0|0|
S11S11S6S23A1S22S16Vn;R4R3A3VJ;R5R3R2A3VJ;R5R4R3A3F_;F_;Fmd;Ftr;Frho';Frho;").

Lemma stableJ_liftK : ltac2:(tb__ "0|0|
S45S6S23A1S22OF_;F_;S4eR2S52R1A1A2FK;Fn;").
Proof using . intros n K rho rho' tr md _ H. exact H. Qed.

Lemma stableJ_mono : ltac2:(tb__ "0|0|
S45S45S4aS47R3R2A2S4eR4R2A2S4eR4R3A2F_;F_;FJ;Fm;Fn;").
Proof using .
  intros n m J Hle H rho rho' tr md Hag HJ. eapply H; [|exact HJ]. eapply agree_below_le; eauto.
Qed.

Lemma ok_frameJ_of_tcons : ltac2:(tb__ "0|1|
S24OF_;S6S23A1M0OF_;S4aS49R3G0S22S27R4R2A2L_;Ltr;A2S11G0S22R5R3R2R1A3S27R7R3A2F_;Fmd;Ftr;Frho;S51R5R3A2F_;F_;FJ;FSpec;Fok;").
Proof using . intros ok Spec J Hok HJ rho tr ms md ms' Hj. apply Hok. eapply HJ; eauto. Qed.

Lemma ok_faultJ_of_tcons : ltac2:(tb__ "0|1|
S24OF_;S6S23A1M0OF_;S4aS4dR3G0S22S27R4R2A2L_;Ltr;A2S11G0S22R5R3R2R1A3S27R7R3A2F_;Fmd;Ftr;Frho;S53R5R3A2F_;F_;FJ;FSpec;Fok;").
Proof using . intros ok Spec J Hok HJ rho tr ms md Hj. apply Hok. eapply HJ; eauto. Qed.

Lemma ok_frame_src : ltac2:(tb__ "0|1|
S6S23A1M0OF_;S49S29Vsegs;R1A2G0S22S27R3R2A2L_;Ltr;A2FSpec;").
Proof using .
  intros Spec tr ms md ms' Hk [Hh Hl] Hp Hs. split; [exact Hk|].
  cbn. intros [_ [[Hp' Hu] | [x8 [Hp' _]]]]; cbn in *; [|congruence].
  rewrite (mi_account_step_lazy_nil segs ms md Hl), Hs in Hu. discriminate.
Qed.

Lemma ok_frame_tgt : ltac2:(tb__ "0|1|
S6S23A1M0OF_;S49S2dVsegs;R1A2G0S22S27R3R2A2L_;Ltr;A2FSpec;").
Proof using .
  intros Spec tr ms md ms' Hk Hh Hp Hs. split; [exact Hk|].
  cbn. intros evs Hst.
  destruct (sstep_error_step ms md evs Hh Hp Hst); congruence.
Qed.

Lemma ok_fault_src : ltac2:(tb__ "0|1|
S6S23A1M0OF_;S4dS29Vsegs;R1A2G0S22S27R3R2A2L_;Ltr;A2FSpec;").
Proof using .
  intros Spec tr ms md Hk [Hh Hl] Hp Hs. split; [exact Hk|].
  cbn. intros [_ [[Hp' Hu] | [x8 [Hp' _]]]]; cbn in *; [|congruence].
  rewrite (mi_account_step_lazy_nil segs ms md Hl), Hs in Hu. discriminate.
Qed.

Lemma sym_load_next : ltac2:(tb__ "0|0|
S10S14S44S7S14S10S0S37S3dVsegs;R6R5R4R3A5S35R2R1A2A3S1S47S12R7A1S12R2A1A2S0S7S13R2A1S13R7A1A3A2F_;FS';Fv;Fsgn;Fk;Fae;FS;").
Proof using .
  intros S ae k sgn v S' H. unfold sym_load in H. lazy zeta in H.
  revert H.
  destruct (match ae with SLit a => ro_load segs (a mod 2 ^ 64) (Z.to_nat k) | _ => None end) as [z|]; intros H.
  { apply lrok_inj in H as [_ <-]. split; [lia | reflexivity]. }
  destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|].
  - assert (LF : forall v' S'', load_fresh S n o off k sgn (8 * Z.to_N k)%N = LROk v' S'' ->
                 (ss_next S <= ss_next S'')%positive /\ ss_lenient S'' = ss_lenient S).
    { intros v' S'' HL. unfold load_fresh, fresh in HL.
      destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; split; try lia; reflexivity. }
    assert (LA : forall v' S'' esz cnt flds tmpl, load_arr S n o off k sgn (8 * Z.to_N k)%N esz cnt flds tmpl = LROk v' S'' ->
                 (ss_next S <= ss_next S'')%positive /\ ss_lenient S'' = ss_lenient S).
    { intros v' S'' esz cnt flds tmpl HL. unfold load_arr in HL.
      destruct (lin_decomp _ _ _) as [[idx c]|]; [|exact (LF _ _ HL)].
      destruct (fld_index flds c k); [|exact (LF _ _ HL)].
      destruct (uleq _ _ _ _); [|exact (LF _ _ HL)].
      apply lrok_inj in HL as [_ <-]. cbn. split; [lia | reflexivity]. }
    assert (LD : forall v' S'', load_dflt S n o off k sgn (8 * Z.to_N k)%N = LROk v' S'' ->
                 (ss_next S <= ss_next S'')%positive /\ ss_lenient S'' = ss_lenient S).
    { intros v' S'' HL. unfold load_dflt in HL. destruct (ob_dflt o); try exact (LF _ _ HL). exact (LA _ _ _ _ _ _ HL). }
    destruct (read_cells (ss_facts S) (ob_cells o) off k CRNone);
      try (apply lrok_inj in H as [_ <-]; split; [lia | reflexivity]); try (exact (LD _ _ H)).
    + destruct (ob_dflt o).
      * exact (LF _ _ H).
      * apply lrok_inj in H as [_ <-]. split; [lia | reflexivity].
      * revert H. destruct (ob_base o) as [zb| | | | | | |]; try (intros H; exact (LF _ _ H)).
        destruct zb; try (intros H; exact (LF _ _ H)).
        destruct off; try (intros H; exact (LF _ _ H)).
        destruct (image_load segs _ (Z.to_nat k)); [|discriminate].
        intros H. apply lrok_inj in H as [_ <-]. split; [lia | reflexivity].
      * apply lrok_inj in H as [_ <-]. split; [lia | reflexivity].
      * apply lrok_inj in H as [_ <-]. split; [lia | reflexivity].
      * exact (LA _ _ _ _ _ _ H).
    + revert H. destruct (tile_cells 9 _ 0 k); intros H; [|exact (LD _ _ H)].
      apply lrok_inj in H as [_ <-]. split; [lia | reflexivity].
  - destruct (ss_lenient S ||| ro_span segs (ss_facts S) ae k); [|discriminate]. unfold fresh in H. apply lrok_inj in H as [_ <-]. cbn. split; [lia | reflexivity].
Qed.

Lemma load_arr_next : ltac2:(tb__ "0|0|
S10SdS19S14S44S7S46S44S14S6SfS44S44A2A1S6S1aA1S14S10S0S37S3aRdRcRbRaR9R8R7R6R5R4R3AbS35R2R1A2A3S1S47S12ReA1S12R2A1A2S0S7S13R2A1S13ReA1A3A2F_;FS';Fv;Ftmpl;Fflds;Fcnt;Fesz;Fw;Fsgn;Fk;Foff;Fo;Fn;FS;").
Proof using .
  intros S n o off k sgn w esz cnt flds tmpl v S' HL. unfold load_arr, load_fresh, fresh in HL.
  destruct (lin_decomp _ _ _) as [[idx c]|].
  2:{ destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; split; try lia; reflexivity. }
  destruct (fld_index flds c k).
  2:{ destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; split; try lia; reflexivity. }
  destruct (uleq _ _ _ _).
  2:{ destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; split; try lia; reflexivity. }
  apply lrok_inj in HL as [_ <-]. cbn. split; [lia | reflexivity].
Qed.

Lemma ss_lenient_set_reg : ltac2:(tb__ "0|0|
S10S48Q5A1S14S0S7S13S34R3R2R1A3A1S13R3A1A3Fv;Fr;FS;").
Proof using . intros. unfold set_reg. destruct (regZ r =? 0); reflexivity. Qed.

Lemma sym_store_shape : ltac2:(tb__ "0|0|
S10S14S44S14S10S0S8S10A1S3eR5R4R3R2A4SbS10R1A2A3S1S0S45S12R2A1S12R6A1A3S0S7S13R2A1S13R6A1A3A2F_;FS';Fv;Fk;Fae;FS;").
Proof using .
  intros S ae k v S' H. unfold sym_store in H.
  destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|]; [|discriminate].
  destruct (dflt_writable (ob_dflt o)); [|discriminate].
  inversion H; subst. split; reflexivity.
Qed.

Lemma sym_step_shape : ltac2:(tb__ "0|6|
S10S2fOLx;S33Vsegs;R1A2S10S1S47S12R2A1M0S12R1A1M1A2S0S7S13R1A1M2S13R2A1M3A3A2LS';S10S10S1S1S47S12R3A1M4G0A2S0S7G3S13R3A1M5A3A2S1S47G4G1A2S0S7G2G5A3A2A2LS2;LS1;S32S3Lr;X2fx3FS;").
Proof using .
  intros S. unfold sym_step.
  destruct (instr_at segs (ss_pc S)) as [i|]; [|exact I].
  destruct i; try exact I; cbn [ss_next ss_lenient set_pc]; rewrite ?ss_next_set_reg, ?ss_lenient_set_reg; try (split; [lia | reflexivity]).
  - destruct (mk_addk (get_reg S rs1) (immI imm)); try exact I. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia | reflexivity].
  - destruct (decide_branch S c (get_reg S rs1) (get_reg S rs2)); cbn; repeat split; lia || reflexivity.
  - destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) (msz sz) signed) as [v S'|] eqn:Hl; [|exact I].
    cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. eapply sym_load_next; eauto.
  - destruct (ss_resv S); [exact I|].
    destruct (sym_store S _ _ _) as [S'|] eqn:Hs; [|exact I]. cbn.
    destruct (sym_store_shape _ _ _ _ _ Hs) as [-> ->]. split; [lia | reflexivity].
  -   destruct (addr_aligned _ _ _); [|exact I]. cbn [negb].
    destruct (sym_load segs S (get_reg S rs1) (amo_k w) true) as [v S'|] eqn:Hl; [|exact I].
    cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. eapply sym_load_next; eauto.
  -   destruct (addr_aligned _ _ _); [|exact I]. cbn [negb].
    destruct (ss_resv S) as [e|].
    + destruct (sv_eqb e (get_reg S rs1)); [|exact I].
      destruct (sym_store (set_resv S None) _ _ _) as [S'|] eqn:Hs; [|exact I]. cbn.
      rewrite ss_next_set_reg, ss_lenient_set_reg.
      destruct (sym_store_shape _ _ _ _ _ Hs) as [-> ->]. cbn. split; [lia | reflexivity].
    + cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia | reflexivity].
  -   unfold sym_csr. destruct (ss_fcsr S); [|exact I].
    destruct ((bv_unsigned csr =? 2) && _)%bool; [cbn; rewrite ss_next_set_reg, ss_lenient_set_reg; split; [lia | reflexivity]|].
    destruct (bv_unsigned csr =? 1); [|exact I]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
  -   unfold sym_csr. destruct (ss_fcsr S); [|exact I].
    destruct ((bv_unsigned csr =? 2) && _)%bool; [cbn; rewrite ss_next_set_reg, ss_lenient_set_reg; split; [lia | reflexivity]|].
    destruct (bv_unsigned csr =? 1); [|exact I]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
  -   destruct fmt.
    + destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) 4 false) as [v S'|] eqn:Hl; [|exact I].
      cbn. eapply sym_load_next; eauto.
    + destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) 8 true) as [v S'|] eqn:Hl; [|exact I].
      cbn. eapply sym_load_next; eauto.
  -   destruct (ss_resv S); [exact I|].
    destruct (sym_store S _ _ _) as [S'|] eqn:Hs; [|exact I]. cbn.
    destruct (sym_store_shape _ _ _ _ _ Hs) as [-> ->]. split; [lia | reflexivity].
  -   destruct (rm_ok S rm); [|exact I]. cbn. split; [lia | reflexivity].
  -   destruct (rm_ok S rm); [|exact I]. cbn. split; [lia | reflexivity].
  -   destruct (rm_ok S rm); [|exact I]. cbn. split; [lia | reflexivity].
  -   destruct (frm0b S); [|exact I]. cbn. split; [lia | reflexivity].
  -   destruct (frm0b S); [|exact I]. cbn. split; [lia | reflexivity].
  -   destruct (frm0b S); [|exact I]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
  -   destruct (rm_ok S rm); [|exact I]. cbn [negb].
    destruct (fcvt_fty dst && (fcvt_fty src || fcvt_ity src))%bool; [cbn; split; [lia | reflexivity]|].
    destruct (fcvt_ity dst && fcvt_fty src)%bool; [|exact I]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
  -   destruct dir, fmt; cbn; rewrite ?ss_next_set_reg, ?ss_lenient_set_reg; split; lia || reflexivity.
  -   destruct (frm0b S); [|exact I]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
Qed.

Lemma sym_step_next : ltac2:(tb__ "0|3|
S10S2fOLx;S33Vsegs;R1A2S10S47S12R2A1M0S12R1A1M1A2LS';S10S10S1S47S12R3A1M2G0A2S47G2G1A2A2LS2;LS1;S32S3Lr;X2fx3FS;").
Proof using .
  intros S. pose proof (sym_step_shape S) as H.
  destruct (sym_step segs S); [exact (proj1 H) | exact (conj (proj1 (proj1 H)) (proj1 (proj2 H))) | exact I].
Qed.

Lemma sym_step_lenient : ltac2:(tb__ "0|3|
S10S2fOLx;S33Vsegs;R1A2S10S0S7S13R1A1M0S13R2A1M1A3LS';S10S10S1S0S7G1S13R3A1M2A3S0S7G0G2A3A2LS2;LS1;S32S3Lr;X2fx3FS;").
Proof using .
  intros S. pose proof (sym_step_shape S) as H.
  destruct (sym_step segs S); [exact (proj2 H) | exact (conj (proj2 (proj1 H)) (proj2 (proj2 H))) | exact I].
Qed.

Definition SPJ (J : jpred) (S : sstate) (rho : valuation) : assn := ltac2:(tb__ "0|0|
S24S1S15Vsegs;Vrho;VS;R1A4VJ;Vrho;S2cR1A1S41S2bR1A1A1A3A2Lw;").

Definition LQJ (J : jpred) (n : positive) (rho : valuation) (leaves : list leaf) : assn := ltac2:(tb__ "0|0|
S24S4S2eS2eS4S11S11S1S55S2eR2Vleaves;A3S1S16Vn;Vrho;R1A3S1S15Vsegs;R1S39R2A1R3A4VJ;R1S2cR3A1S41S2bR3A1A1A3A2A2A2Lrho';A2LL;A2Lw;").

Definition SP (K : list event -> Model -> Prop) (S : sstate) (rho : valuation) : assn := ltac2:(tb__ "0|0|
S4cS52VK;A1VS;Vrho;A3").

Definition LQ (K : list event -> Model -> Prop) (n : positive) (rho : valuation) (leaves : list leaf) : assn := ltac2:(tb__ "0|0|
S50S52VK;A1Vn;Vrho;Vleaves;A4").

Lemma LQJ_weaken : ltac2:(tb__ "0|1|
S4aS45S45S11S11S6S2eA1M0G0S24S47R7R6A2S16R8R6R5A3S2eS55S2eR1R6A3S55S2eR2R6A3F_;FL;S50RbR9R7R6R4A5S50RcRbR9R6R5A5F_;F_;F_;F_;Fw;Fleaves';Fleaves;Frho';Frho;Fn';Fn;FJ;").
Proof using .
  intros J n n' rho rho' leaves leaves' w Hle Hag Hsub (L & rho'' & Hin & Hag' & Hsm & Hk).
  exists L, rho''. split; [apply Hsub; exact Hin|]. split; [|split; assumption].
  eapply agree_below_trans; [exact Hag|]. eapply agree_below_le; eauto.
Qed.

Lemma LQ_weaken : ltac2:(tb__ "0|1|
S6S23A1S22OF_;F_;S45S45S11S11S6S2eA1M0G0S24S47R7R6A2S16R8R6R5A3S2eS55S2eR1R6A3S55S2eR2R6A3F_;FL;S4fRbR9R7R6R4A5S4fRcRbR9R6R5A5F_;F_;F_;F_;Fw;Fleaves';Fleaves;Frho';Frho;Fn';Fn;FK;").
Proof using . intros K. exact (LQJ_weaken (liftK K)). Qed.

Lemma triple1_branchJ : ltac2:(tb__ "0|1|
S24OF_;S4aS10S10S10S11S51R6R5A2S0S7S13R5A1SaA3S53R8R7A2F_;S4eS12R6A1R7A2S6S23A1M0S1bS22S15Vsegs;R7RaS9G0S40R3S3fR2R1A2A4A4S2S1S0S7S13RbA1SaA3S0S1cS1bA1S1dVsegs;R3A2S1fS1bA1A3A2S2S54Vsegs;RbRaR8R4R3R2A7S54Vsegs;RbR9R8R4R3R2A7A2A2F_;Fmd;Fms;Ftr;S25Vsegs;RaS4cR9R8R5A3S24S4S11S11S1S16S12RaA1R7R1A3S2S4cRbR9R1R2A4S4cRbR8R1R2A4A2A2Lrho';A2Lw;A4F_;F_;F_;F_;Frho;FS2;FS1;FS;FJ;Fok;").
Proof using .
  intros ok J S S1 S2 rho Hok Hokf Hst Hnext. apply triple1_step.
  intros [tr [ms md]] [Hsm Hk]. cbn in Hk.
  pose proof Hsm as (_ & _ & Hpend & Hhalt & _). cbn [fst snd cfg_ms cfg_model] in Hpend, Hhalt.
  destruct (Hnext tr ms md Hsm) as [[Hl Hfault] | [(ms' & rho' & Hstep & Hag & Hle & Hsm') | (ms' & rho' & Hstep & Hag & Hle & Hsm')]].
  - split; [eapply (Hokf Hl); eauto|].
    intros w' Hw. exfalso. exact (wstep_fault_none tr ms md w' Hhalt Hpend Hfault Hw).
  - split; [eapply Hok; eauto|].
    intros w' Hw. rewrite (wstep_step_inv tr ms md ms' w' Hhalt Hpend Hstep Hw).
    exists rho'. split; [exact Hag|]. left. split; [exact Hsm' | eapply Hst; eauto].
  - split; [eapply Hok; eauto|].
    intros w' Hw. rewrite (wstep_step_inv tr ms md ms' w' Hhalt Hpend Hstep Hw).
    exists rho'. split; [exact Hag|]. right. split; [exact Hsm' | eapply Hst; eauto].
Qed.

Lemma sym_run_sound_genJ : ltac2:(tb__ "0|3|
SdS6S44A1S24OF_;S4aS51R2R1A2S10S7S6S2eA1M0S11S0S7S13R4A1SaA3S53R8R7A2F_;S4eS12R5A1R7A2S0S8G0A1S30Vsegs;RbRaR6R5A5SbG0R4A2A3S7OLfirst;R6S25Vsegs;RaS4cR9R7R4A3M1S50R9S12R7A1R4R5A4M2A4S2aVsegs;RaG1G2A4X7x2F_;F_;F_;Frho;Fleaves;Ffirst;FS;F_;FJ;Fok;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts ok J Hok. induction fuel as [|fuel IH]; intros S first leaves rho Hokf Hst Hrun.
  - cbn in Hrun. destruct first; [discriminate|]. inversion Hrun; subst.
    intros n Hg w [Hsm Hk]. apply Hg. exists (mkLeaf S RsFuel), rho.
    split; [left; reflexivity|]. split; [apply agree_below_refl|]. split; assumption.
  - cbn [sym_run] in Hrun.
    assert (Hleaf : forall r, triple segs ok (SPJ J S rho) (LQJ J (ss_next S) rho [mkLeaf S r])).
    { intros r n Hg w [Hsm Hk]. apply Hg. exists (mkLeaf S r), rho.
      split; [left; reflexivity|]. split; [apply agree_below_refl|]. split; assumption. }
    destruct (negb first && memZ (ss_pc S) cuts)%bool eqn:Hcut.
    + destruct first; [discriminate|]. inversion Hrun; subst. apply Hleaf.
    + pose proof (sym_step_next S) as Hmono. pose proof (sym_step_lenient S) as Hlen.
      assert (Hgo : forall S1 S2 l1 l2,
                (ss_next S <= ss_next S1)%positive -> (ss_next S <= ss_next S2)%positive ->
                ss_lenient S1 = ss_lenient S -> ss_lenient S2 = ss_lenient S ->
                (forall tr ms md, smatch segs rho S (tr, mkCfg ms md) ->
                   (ss_lenient S = true /\ RiscvSemantics.step segs ms = MachineFault)
                   \/ next_rel segs S S1 rho tr ms md \/ next_rel segs S S2 rho tr ms md) ->
                sym_run segs fuel cuts S1 false = Some l1 ->
                sym_run segs fuel cuts S2 false = Some l2 ->
                (forall L, In L l1 -> In L leaves) -> (forall L, In L l2 -> In L leaves) ->
                triple1 segs ok (SPJ J S rho) (LQJ J (ss_next S) rho leaves)).
      { intros S1 S2 l1 l2 Hle1 Hle2 Hl1 Hl2 Hnext Hr1 Hr2 Hs1 Hs2.
        eapply triple1_seq_l; [apply triple1_branchJ; [exact Hok | exact Hokf | exact Hst | exact Hnext]|].
        apply triple_ex. intros rho'. apply triple_pure. intros Hag.
        apply triple_disj.
        - eapply triple_conseq; [intros w Hw; exact Hw | | exact (IH S1 false l1 rho' ltac:(rewrite Hl1; exact Hokf) (stableJ_mono _ _ _ Hle1 Hst) Hr1)].
          intros w HQ. exact (LQJ_weaken J _ _ rho rho' l1 leaves w Hle1 Hag Hs1 HQ).
        - eapply triple_conseq; [intros w Hw; exact Hw | | exact (IH S2 false l2 rho' ltac:(rewrite Hl2; exact Hokf) (stableJ_mono _ _ _ Hle2 Hst) Hr2)].
          intros w HQ. exact (LQJ_weaken J _ _ rho rho' l2 leaves w Hle2 Hag Hs2 HQ). }
      destruct (sym_step segs S) as [S'|S1 S2|r] eqn:Hss.
      * assert (T : triple1 segs ok (SPJ J S rho) (LQJ J (ss_next S) rho leaves)).
        { apply (Hgo S' S' leaves leaves); auto.
          intros tr ms md Hsm. pose proof (sym_step_sound S rho tr ms md Hsm) as X. rewrite Hss in X.
          destruct X as [F | N]; [left; exact F | right; left; exact N]. }
        destruct first; [exact T | apply triple1_triple; exact T].
      * destruct (sym_run segs fuel cuts S1 false) as [l1|] eqn:H1; [|discriminate].
        destruct (sym_run segs fuel cuts S2 false) as [l2|] eqn:H2; [|discriminate].
        inversion Hrun; subst.
        destruct Hmono as [Hle1 Hle2]. destruct Hlen as [Hl1 Hl2].
        assert (T : triple1 segs ok (SPJ J S rho) (LQJ J (ss_next S) rho (l1 ++ l2))).
        { apply (Hgo S1 S2 l1 l2); auto.
          - intros tr ms md Hsm. pose proof (sym_step_sound S rho tr ms md Hsm) as X. rewrite Hss in X. right. exact X.
          - intros L HL. apply in_or_app. left. exact HL.
          - intros L HL. apply in_or_app. right. exact HL. }
        destruct first; [exact T | apply triple1_triple; exact T].
      * destruct first; [discriminate|]. inversion Hrun; subst. apply Hleaf.
Qed.

Theorem sym_run_soundJ : ltac2:(tb__ "0|1|
SdS6S44A1S10S6S2eA1M0S24OF_;S4aS11S0S8G0A1S30Vsegs;R7R6R5SaA5SbG0R4A2A3S51R4R3A2S0S7S13R7A1SaA3S53R6R5A2F_;S4eS12R8A1R5A2S25Vsegs;R7S4cR6R9R5A3S50R6S12R9A1R5R8A4A4F_;F_;F_;F_;Frho;FJ;Fok;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves ok J rho Hrun Hok Hokf Hst.
  exact (sym_run_sound_genJ fuel cuts ok J Hok S true leaves rho Hokf Hst Hrun).
Qed.

Lemma triple1_branch : ltac2:(tb__ "0|1|
S24OF_;S6S23A1M0S22OF_;F_;S10S10S10S11S49R6R5A2S0S7S13R5A1SaA3S4dR8R7A2F_;G0S1bS22S15Vsegs;R6R9S9G0S40R3S3fR2R1A2A4A4S2S1S0S7S13RaA1SaA3S0S1cS1bA1S1dVsegs;R3A2S1fS1bA1A3A2S2S54Vsegs;RaR9R7R4R3R2A7S54Vsegs;RaR8R7R4R3R2A7A2A2F_;Fmd;Fms;Ftr;S25Vsegs;R9S4bR8R7R4A3S24S4S11S11S1S16S12R9A1R6R1A3S2S4bRaR8R1R2A4S4bRaR7R1R2A4A2A2Lrho';A2Lw;A4F_;F_;F_;Frho;FS2;FS1;FS;FK;Fok;").
Proof using .
  intros ok K S S1 S2 rho Hok Hokf Hnext.
  exact (triple1_branchJ ok (liftK K) S S1 S2 rho (ok_frame_liftK ok K Hok)
           (fun H => ok_fault_liftK ok K (Hokf H)) (stableJ_liftK _ K) Hnext).
Qed.

Lemma sym_run_sound_gen : ltac2:(tb__ "0|3|
SdS6S44A1S24OF_;S6S23A1S22OF_;F_;S49R2R1A2S10S7S6S2eA1M0S11S0S7S13R4A1SaA3S4dR8R7A2F_;S0S8G0A1S30Vsegs;RaR9R5R4A5SbG0R3A2A3S7OLfirst;R5S25Vsegs;R9S4bR8R6R3A3M1S4fR8S12R6A1R3R4A4M2A4S2aVsegs;R9G1G2A4X7x2F_;F_;Frho;Fleaves;Ffirst;FS;F_;FK;Fok;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts ok K Hok S first leaves rho Hokf Hrun.
  exact (sym_run_sound_genJ fuel cuts ok (liftK K) (ok_frame_liftK ok K Hok) S first leaves rho
           (fun H => ok_fault_liftK ok K (Hokf H)) (stableJ_liftK _ K) Hrun).
Qed.

Theorem sym_run_sound : ltac2:(tb__ "0|1|
SdS6S44A1S10S6S2eA1M0S24OF_;S6S23A1S22OF_;F_;S11S0S8G0A1S30Vsegs;R7R6R5SaA5SbG0R4A2A3S49R4R3A2S0S7S13R7A1SaA3S4dR6R5A2F_;S25Vsegs;R6S4bR5R8R4A3S4fR5S12R8A1R4R7A4A4F_;F_;F_;Frho;FK;Fok;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves ok K rho Hrun Hok Hokf.
  exact (sym_run_sound_gen fuel cuts ok K Hok S true leaves rho Hokf Hrun).
Qed.

Corollary sym_run_sound_strict : ltac2:(tb__ "0|1|
SdS6S44A1S10S6S2eA1M0S24OF_;S6S23A1S22OF_;F_;S11S0S7S13R5A1SeA3S0S8G0A1S30Vsegs;R8R7R6SaA5SbG0R5A2A3S49R5R4A2S25Vsegs;R6S4bR5R8R4A3S4fR5S12R8A1R4R7A4A4F_;F_;F_;Frho;FK;Fok;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves ok K rho Hl Hrun Hok. apply (sym_run_sound fuel cuts S leaves ok K rho Hrun Hok). congruence.
Qed.

Corollary sym_run_soundJ_strict : ltac2:(tb__ "0|1|
SdS6S44A1S10S6S2eA1M0S24OF_;S4aS11S0S7S13R5A1SeA3S0S8G0A1S30Vsegs;R8R7R6SaA5SbG0R5A2A3S51R5R4A2S4eS12R8A1R5A2S25Vsegs;R7S4cR6R9R5A3S50R6S12R9A1R5R8A4A4F_;F_;F_;F_;Frho;FJ;Fok;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves ok J rho Hl Hrun Hok Hst. apply (sym_run_soundJ fuel cuts S leaves ok J rho Hrun Hok); [congruence|exact Hst].
Qed.

Corollary sym_run_sound_fault : ltac2:(tb__ "0|1|
SdS6S44A1S10S6S2eA1M0S24OF_;S6S23A1S22OF_;F_;S11S0S8G0A1S30Vsegs;R7R6R5SaA5SbG0R4A2A3S49R4R3A2S4dR5R4A2S25Vsegs;R6S4bR5R8R4A3S4fR5S12R8A1R4R7A4A4F_;F_;F_;Frho;FK;Fok;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves ok K rho Hrun Hok Hokf. apply (sym_run_sound fuel cuts S leaves ok K rho Hrun Hok). intros _; exact Hokf.
Qed.

End R.
