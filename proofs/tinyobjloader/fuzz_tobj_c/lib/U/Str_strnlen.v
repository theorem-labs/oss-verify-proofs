(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "option"; "false"; "true"; "None"; "bool"; "Some"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SVar"; "SLit"; "sobj"; "SPUle"; "sstate"; "cell"; "sv"; "valuation"; "FcsrFrm0"; "SAlu"; "SPBranch"; "mkCell"; "mkSS"; "DUnknown"; "mkObj"; "ss_next"; "SPAlign"; "SPEq"; "agree_below"; "holds"; "ss_facts"; "ss_lenient"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "two62"; "pre_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen"; "Pre_strnlen"; "E_call"; "s_call"; "R_fr"; "FUELN"; "O_stack_post"; "P_strnlen"; "Posts_strnlen"; "T_imp"; "X_null"; "cuts_sn"; "sn_post_facts"; "O_stack"; "R_call"; "exits_sn"; "sn_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "list_set"; "RsSymJump"; "lf_state"; "mkLeaf"; "sym_run"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "False"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr"; "FirstNul"; "O_str"; "Pre_memchr0"; "P_ret"; "Posts_memchr0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "BC_EQ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memchr_entry"; "strnlen_ret"; "strnlen_entry"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "check_cfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@Stdlib.Lists.List"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv StrBytes CfgGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code Str_memchr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUELN : nat := 200%nat.
Definition O_stack (k : Z) : sobj := ltac2:(tb__ "0|0|
S18SaPaA1SbS5cVk;A1A1SbZ0A1S1SfA1S17A5").
Definition sn_facts : list sprop := ltac2:(tb__ "0|6|
S0S9S14S45SaP10A1M0SaPdA1M1A3S0S9SdS13S44G0SbZ8A1M2A3SaP11A1M3A2S0S9SdG2G3A2S0S9SdG3SbS24A1M4A2S0S9SdG1G4A2S0S9SdSbZ1A1SaPcA1M5A2S0S9SdG5G4A2S0S9S1aPaZ4A2S1S9A1A3A3A3A3A3A3A3A3").
Definition Pre_strnlen : sstate := ltac2:(tb__ "0|0|
S16S49S25S22S12S6S10A1S0ScS40S0ScS32Z20A1S1ScA1A3A3S35S21S4A9").

Definition R_call : ltac2:(tb__ "0|0|
S3S2S36A1A1") := ltac2:(tb__ "0|0|
S3bS20S2aS0S3cS47S1S3cA1A3S26S5A5").
Definition R_call__f : ltac2:(tb__ "0|0|
S3S2S36A1A1") := ltac2:(tb__ "0|0|
S5aS20S2aS0S3cS47S1S3cA1A3S26S5A5").
Definition E_call : sstate := ltac2:(tb__ "0|1|
S3S2S36A1M0A1SeLx;S33G0G0SeLl;R1S26S36G0G0SeLl0;R1S39R2A1S36G0S26Ll2;Ll1;X2x2Ll0;LL;X2x2Ll;S26X3x2").
Definition s_call : wsub := infer_sub 10 E_call Pre_memchr0.
Definition R_fr : list sobj := ltac2:(tb__ "0|1|
S3S2ScA1M0A1G0Lx;S4cS27S41S28A3G0R1LR;S1ScA1X3x2").
Definition T_imp : sstate := ltac2:(tb__ "0|0|
S50S28S21S42S19S27A1S29A5").

Definition sn_post_facts : list sprop := ltac2:(tb__ "0|6|
S0S9S1bSaP8cA1SaP10A1M0A2S0S9S14S45G0SaPdA1M1A3S0S9SdS13S44G0SbZ8A1M2A3SaP11A1M3A2S0S9SdG2G3A2S0S9SdG3SbS24A1M4A2S0S9SdG1G4A2S0S9SdSbZ1A1SaPcA1M5A2S0S9SdG5G4A2S1S9A1A3A3A3A3A3A3A3A3").
Definition O_stack_post : sobj := ltac2:(tb__ "0|1|
S18SaPaA1SbN20A1SbZ0A1S0SfS15SbN18A1Z8M0SaP1dA1A3S0SfS15SbN10A1G0SaP1cA1A3S0SfS15SbN8A1G0SaPbA1A3S1SfA1A3A3A3S17A5").
Definition P_strnlen : sstate := ltac2:(tb__ "0|0|
S16S48S37S10S23S21A1UaSaP8cA1A4S22S12S6S10A1S0ScS40S0ScS2bS1ScA1A3A3S31P8dS4A9").
Definition Posts_strnlen : list leaf := ltac2:(tb__ "0|0|
S0S36S3aS2cS38A2S1S36A1A3").

Definition X_null : sstate := ltac2:(tb__ "0|0|
S16S48S37S10S23S21A1UaSaPdA1A4S22S12S6S10A1S0ScS40S0ScS2bS1ScA1A3A3S0S9S14S46S13S44SaPcA1SaP8cA1A3SbZ0A1A3S31A3P8dS4A9").

Definition cuts_sn : list sstate := ltac2:(tb__ "0|0|
S0SeS26S0SeS2eS1SeA1A3A3").
Definition exits_sn : list sstate := ltac2:(tb__ "0|0|
S0SeS27S0SeS2cS0SeS2fS1SeA1A3A3A3").

Lemma check_sn : ltac2:(tb__ "0|0|
S3dS7S57S20S2aS0S3cS47S1S3cA1A3S21S30S34A6S5A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_sn_strict : ltac2:(tb__ "0|0|
S3dS7S5bSeS1fS30A3S4A3").
Proof. vm_compute. reflexivity. Qed.
Lemma efr_call : ltac2:(tb__ "0|1|
S3dS3S2ScA1M0A1S4cS27S41S28A3S8G0S29A2A3").
Proof. vm_compute. reflexivity. Qed.
Lemma chk_call : ltac2:(tb__ "0|0|
S3dS7S51S27S41S28S29S43A5S5A3").
Proof. vm_compute. reflexivity. Qed.
Lemma next_call : ss_next E_call = NF.
Proof. vm_compute. reflexivity. Qed.
Lemma imp_call : ltac2:(tb__ "0|0|
S3dSeS50S28S21S42S19S27A1S29A5S2eA3").
Proof. reflexivity. Qed.
Lemma s_call_16 : wsub_get s_call 16 = SVar 16.
Proof. vm_compute. reflexivity. Qed.

Lemma FirstNul_call : ltac2:(tb__ "0|0|
S11S2ScA1S53S3fR3A1S3fS59S58R4R3R2A3S28A2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. unfold FirstNul. rewrite rl_call, rw_call, s_call_16. cbn [eval]. split; assumption.
Qed.

Lemma contra_null : ltac2:(tb__ "0|0|
S11S11S1cS21R2R1A3S52S9S1dR2A1S1eS2fA1A3S3eF_;F_;Frho;Frho0;").
Proof.
  intros rho0 rho _ HF. unfold X_null in HF. cbn [ss_facts] in HF. unfold sn_post_facts in HF.
  apply Forall_cons_iff in HF as [Hnull HF]. apply Forall_cons_iff in HF as [Heq HF].
  apply Forall_cons_iff in HF as [Hzn HF]. apply Forall_cons_iff in HF as [_ HF].
  apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [_ HF].
  apply Forall_cons_iff in HF as [Hn HF]. apply Forall_cons_iff in HF as [Hs1 HF].
  apply Forall_cons_iff in HF as [Hs2 _].
  pose proof (urange (rw rho 12)) as R12. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 13)) as R13.
  cbn [holds eval branch_taken] in Hnull, Heq, Hzn, Hn, Hs1, Hs2. unfold bv_ltu, bv_eqb in *.
  rewrite add_val, lit_unsigned in Hnull. rewrite ?lit_unsigned, ?two62_mod in Hn, Hs1, Hs2.
  apply Z.eqb_eq in Hnull. apply Z.ltb_lt in Hzn.
  change (0 mod 2 ^ 64) with 0 in Hnull. change (1 mod 2 ^ 64) with 1 in Hs1.
  rewrite two62_mod in Hn. rewrite two62_mod in Hs2.
  rewrite Heq in Hnull. rewrite Z.mod_small in Hnull by lia. lia.
Qed.

Theorem strnlen_sum : ltac2:(tb__ "0|0|
S56OF_;S2S4bA1S4aOF_;F_;S11S4fS20R3R2A3S3fR2A1S55S20R5S4eS20R4S26R3A4S4dS20R4S21R3S2dA5A4F_;F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok HFN.
  apply (cfg_sound segs FUELN [memchr_entry] NF cuts_sn exits_sn
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_strnlen) Hok).
  - rewrite cuts_sn_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_sn.
  - intros E rhoE HinE HagE. destruct HinE as [<-|[<-|[<-|[]]]].
    +
      apply (call_sound_P segs FirstNul ok K K E_call Pre_memchr0 s_call R_fr Posts_memchr0);
        [exact efr_call | exact chk_call | | |].
      * intros rho1 HF1. apply memchr0_sum; [exact Hok | exact HF1].
      * intros ms. apply FirstNul_call. eapply FirstNul_agree; [| exact HagE | exact HFN]. reflexivity.
      * intros L rho' HinL Hag'. rewrite next_call in Hag'.
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hsp. left. destruct HinL as [<-|[]].
        exists T_imp, rho'. split; [right; left; reflexivity|]. split; [eapply agree_below_trans; eauto | exact Hsp].
    + apply exit_post; [left; reflexivity | exact HagE].
    + revert HagE. apply (exit_contra segs ok K _ X_null). exact (contra_null rho).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem strnlen_sum_ex : ltac2:(tb__ "0|0|
S2S4bA1S4aOF_;F_;S11S3fR1A1S54S20S4eS20R3S26R2A4S4dS20R3S21R2S2dA5A3F_;Frho;FK;").
Proof.
  intros K rho HFN.
  change Pre_strnlen with (vn_state (mkVN Pre_strnlen 10 (SLit 0))).
  apply (cfg_complete_auto segs FUELN [memchr_entry] NF
           [mkVN Pre_strnlen 10 (SLit 0); mkVN T_imp 3 (SLit 0)]
           [mkVN E_call 5 (SLit 0); mkVN P_strnlen 0 (SLit 0); mkVN X_null 0 (SLit 0)]
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_strnlen)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - vm_compute. reflexivity.
  - intros E rhoE HinE HgE. destruct HinE as [<-|[<-|[<-|[]]]].
    + cbn [vn_state].
      apply (call_complete_P segs FirstNul K K E_call Pre_memchr0 s_call R_fr Posts_memchr0);
        [exact efr_call | exact chk_call | | |].
      * intros rho1 HF1. apply memchr0_sum_ex. exact HF1.
      * intros ms. apply FirstNul_call. eapply FirstNul_agree; [| exact HgE | exact HFN]. reflexivity.
      * intros L rho' HinL Hag'. rewrite next_call in Hag'.
        intros w Hsp. exists w. split; [apply wsteps_refl|]. left. destruct HinL as [<-|[]].
        exists (to_enode (fun rho' => agree_below NF rho rho') (mkVN T_imp 3 (SLit 0))), rho'.
        split; [right; left; reflexivity|]. cbn [to_enode en_state en_ghost en_meas fst snd vn_state].
        split; [eapply agree_below_trans; eauto|]. split; [exact Hsp|].
        unfold vmeas. cbn [vn_rank vn_var eval]. rewrite !lit_unsigned. cbn. lia.
    + apply eexit_post; [left; reflexivity | exact HgE].
    + revert HgE. cbn [vn_state]. apply (eexit_contra segs K _ X_null). exact (contra_null rho).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
