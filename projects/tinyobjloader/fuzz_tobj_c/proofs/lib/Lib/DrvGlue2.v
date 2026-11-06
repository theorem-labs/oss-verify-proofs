(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sstate"; "eval"; "reg_sv"; "obj_holds"; "obj_range"; "obj_wf"; "odefault"; "smatch"; "ss_objs"; "DUnknown"; "SLit"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "rom_ok"; "ss_next"; "ss_pc"; "sv"; "tfact"; "@Corelib.Init.Logic"; "eq"; "ex"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "option"; "nat"; "prod"; "Some"; "false"; "S"; "app"; "cons"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2.WithSegs"; "obj_forget_of"; "obj_forget"; "forgettable"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "ENOTTY"; "FdChannel"; "errno_ret"; "fd_lookup"; "m_fds"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "cmd32"; "fd32"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "TIOCGWINSZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "nth_error"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame SymBytes SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import DrvGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition forgettable (d : odefault) : bool := ltac2:(tb__ "0|0|
S8S1bLd;Vd;S1aS1aS1aS26S1aLl;S26S21Ll;S25S16S1cS1fS25S25A2A1S1cS17A1S21Ltmpl;Lflds;Lcnt;Lesz;X8x6").

Definition obj_forget_of (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1bS0L_;S2cS10Vo;A1A1SdSeVo;A1S12Vo;A1S11Vo;A1SfVo;A1SbA5Vo;X1bx2").

Definition obj_forget (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S1dS0A1S2Lx;S43S0SaVS;A1M0Vi;A3S0S42VS;S23S0S39S0Vi;G0A3S24S0S2aR1A1S3aS0S22Vi;A1G0A3A3A3A2Lo;VS;X1dx2").

Lemma obj_holds_forget_of : ltac2:(tb__ "0|0|
S1S3bS0S13Vsegs;R2A2S5Vsegs;R4R3R2A4S5Vsegs;R5R4S2aR3A1A4F_;F_;Fo;Fms;Frho;").
Proof using .
  intros rho ms o Hrom Ho. unfold obj_forget_of. destruct (forgettable (ob_dflt o)) eqn:E; [|exact Ho].
  pose proof Ho as (Hb & Hw & Hc & Hdf & Hinv).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split.
  { intros off Hoff _. apply Hw; [exact Hoff|]. destruct (ob_dflt o); try reflexivity; discriminate E. }
  split; [exact Hc|]. split; [|exact I].
  intros off Hoff Hnc. cbn [dflt_holds]. pose proof (Hdf off Hoff Hnc) as D.
  destruct (ob_dflt o); cbn [dflt_holds] in D; try discriminate E.
  - exact D.
  - eexists. exact D.
  - destruct D as [Hm [b Hi]]. exists b. unfold rd, ms_read_byte. rewrite Hm, (Hrom _). exact Hi.
  - eexists. exact D.
Qed.

Lemma obj_range_forget_of : ltac2:(tb__ "0|0|
S1S0S18S1fS25S25A2S6R2S2aR1A1A2S6R2R1A2A3Fo;Frho;").
Proof using . intros rho o. unfold obj_forget_of. destruct (forgettable (ob_dflt o)); reflexivity. Qed.

Lemma obj_wf_forget_of : ltac2:(tb__ "0|0|
S26S0S18S1bS7R2R1A2S1aA3S18S1bS7R3S2aR2A1A2S1aA3F_;Fo;Fn;").
Proof using .
  intros n o H. unfold obj_forget_of. destruct (forgettable (ob_dflt o)) eqn:E; [|exact H].
  unfold obj_wf in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. cbn [dflt_wf].
  apply andb_prop in H as [H _]. rewrite H. reflexivity.
Qed.

Theorem smatch_obj_forget : ltac2:(tb__ "0|0|
S1S2S1fS1cS2eA1S3cA2S1eS9Vsegs;R4R3R2A4S9Vsegs;R5S2bR4R2A2R3A4F_;Fi;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] i Hsm. unfold obj_forget.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|exact Hsm].
  pose proof Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 (ss_objs S) i o Hn) as Esplit.
  set (L1 := firstn i (ss_objs S)) in *. set (L2 := skipn (Datatypes.S i) (ss_objs S)) in *.
  assert (Hmm : mem_match segs rho (L1 ++ obj_forget_of o :: L2) ms).
  { rewrite Esplit in Hm. destruct Hm as (Hall & Hpd & Hfr). split; [|split].
    - apply Forall_app in Hall as [H1 H2]. inversion H2 as [|x l Ho H3]; subst.
      apply Forall_app. split; [exact H1|]. constructor; [apply obj_holds_forget_of; [exact Hrom | exact Ho] | exact H3].
    - eapply pairwise_disjoint_Forall2; [|exact Hpd].
      apply Forall2_app; [apply Forall2_refl_ranges|]. constructor; [apply obj_range_forget_of | apply Forall2_refl_ranges].
    - intros a Ha. apply Hfr. eapply outside_all_Forall2; [|exact Ha].
      apply Forall2_app; [apply Forall2_refl_ranges|]. constructor; [apply obj_range_forget_of | apply Forall2_refl_ranges]. }
  unfold smatch, set_objs. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
  split.
  { unfold swf in *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    rewrite Esplit in Hswf. rewrite forallb_app in Hswf |- *. cbn [forallb] in Hswf |- *.
    apply andb_prop in Hswf as [Hswf F8]. apply andb_prop in Hswf as [Hswf F7].
    apply andb_prop in F7 as [F7a F7]. apply andb_prop in F7 as [F7b F7c].
    rewrite Hswf, F8, F7a, F7c, (obj_wf_forget_of _ _ F7b). reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [exact Hmm|exact Hfa].
Qed.

Lemma SPJ_obj_forget : ltac2:(tb__ "0|0|
S29S1S2S1eS37S28Vsegs;R5R3R4R1A5S28Vsegs;R6S2bR4R3A2R5R2A5F_;Fw;Fi;FS;Frho;FJ;").
Proof using . intros J rho S i w [Hsm HJ]. split; [apply smatch_obj_forget; exact Hsm | exact HJ]. Qed.
Lemma SP_obj_forget : ltac2:(tb__ "0|0|
S1cS2eA1S2dOF_;F_;S1S2S1eS37S27Vsegs;R5R3R4R1A5S27Vsegs;R6S2bR4R3A2R5R2A5F_;Fw;Fi;FS;Frho;FK;").
Proof using . intros K rho S i w [Hsm HK]. split; [apply smatch_obj_forget; exact Hsm | exact HK]. Qed.

Lemma etriple_ioctl : ltac2:(tb__ "0|3|
S1cS2eA1M0S2dOFx0;Fx;S2S1S18S1dS35A1S41Vsegs;S15R2A1A2S20S35S36A2A3S18S45Q40M1A1M2S3R2S4R3Z11A2A2S44G1Z1dA2A3G0S2dR7R2R1A2S19G2G2S18S1dS2fA1S33S34R3A1S3eS3R7S4R8ZaA2A2A1A2S20S2fS31R1A1A2A3Le;A2F_;Fmd;Ftr;S18G2S3dS3R4S4R5ZbA2A2A1S3fA3S38Vsegs;S27Vsegs;R7R6R5A4S27Vsegs;R7S40R6ScS46G1S32S30A1A2A1SaR6A1S14R6A1A4R5A4A3F_;F_;F_;F_;Frho;FS;FK;").
Proof using .
  intros K S rho Hi H17 Hfd Hcmd.
  eapply etriple_ecall_det; [exact Hi|].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp.
  pose proof (smatch_pending_halted _ _ _ _ _ _ Hsp) as Hh.
  destruct (Hfd tr md Hk) as [e He].
  pose proof (smatch_pending_gpr _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0.
  pose proof (smatch_pending_gpr _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  rewrite <- G0 in He. pose proof Hcmd as Hc. rewrite <- G1 in Hc.
  assert (H29 : bv_unsigned (Z_to_bv 64 29) = 29) by reflexivity.
  eexists. split; [exact (@wstep_ioctl_intro segs tr ms md _ e Hp Hh H29 He Hc)|].
  split; [|exact Hk]. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

End WithSegs.
