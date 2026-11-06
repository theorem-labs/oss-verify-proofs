(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@Corelib.Init.Datatypes"; "option"; "Some"; "list"; "bool"; "false"; "pair"; "length"; "nil"; "None"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "reg_sv"; "rl"; "sobj"; "rw"; "soff"; "ss_next"; "DList"; "cell"; "mkObj"; "rm"; "ss_objs"; "smatch"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysReadList.WithSegs.ReadList"; "rl_rho'"; "rl_bs"; "rl_S'"; "rl_md'"; "rl_new"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "FdEntry"; "Model"; "m_fds"; "FdFile"; "event"; "fd_lookup"; "m_fs"; "MAX_RW_COUNT"; "TASK_SIZE"; "read_bytes_map"; "fd_insert"; "with_fds"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "to_nat"; "of_nat"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "file_read"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_writable_byte"; "ms_mem"; "ms_svc_pending"; "write_to_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "sv_has_rl"; "smatch_pending"; "ok_pframeJ"; "rho_set_rl"; "rho_set_rw"; "state_has_rl"; "@Corelib.Lists.ListDef"; "skipn"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "model_idle"; "triple1"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_var"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi Fs.File.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SysRead.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Section ReadList.
Variable S : sstate.
Variable rho : valuation.
Variable k : nat.
Variables base elo ehi : sv.
Variables p data : list byte.
Variable off : Z.
Variables l0 l : positive.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S8S4dA1S55Vsegs;S1fVS;A1A2S9S4dS4eA2A3").
Hypothesis H17 : reg_sv S 17 = SLit 63.
Hypothesis H10 : reg_sv S 10 = SLit 3.
Hypothesis Hoff : 0 <= off < 2 ^ 64.
Hypothesis Hcnt : ltac2:(tb__ "0|0|
S31S5Q40S12Vrho;S13VS;ZcA2A2A2S2cA2").
Hypothesis Hov : ltac2:(tb__ "0|1|
S31S32S5Q40M0S12Vrho;S13VS;ZbA2A2A2S5G0S12Vrho;S13VS;ZcA2A2A2A2S2dA2").
Hypothesis Hnth : ltac2:(tb__ "0|0|
S0S8S15A1S58S15S1dVS;A1Vk;A3S9S15S1bVbase;Velo;Vehi;SfS1aA1S19Vl0;A1A5A2A3").

Hypothesis Hbuf : ltac2:(tb__ "0|1|
S0S3aS5Q40M0S12Vrho;S13VS;ZbA2A2A2S32S5G0S12Vrho;Vbase;A2A2S17Vrho;Velo;A2A2A3").

Hypothesis Hhi : ltac2:(tb__ "0|0|
S31S32S17Vrho;Velo;A2S5Q40S12Vrho;S13VS;ZcA2A2A2A2S17Vrho;Vehi;A2A2").
Hypothesis Hnorl : ltac2:(tb__ "0|0|
S0SbS4aVl;VS;A2ScA3").
Hypothesis Hnob : ltac2:(tb__ "0|0|
S0SbS45Vl;Vbase;A2ScA3").
Hypothesis Hnolo : ltac2:(tb__ "0|0|
S0SbS45Vl;Velo;A2ScA3").
Hypothesis Hnohi : ltac2:(tb__ "0|0|
S0SbS45Vl;Vehi;A2ScA3").
Hypothesis Hll : l <> l0.

Definition rl_bs : list byte := ltac2:(tb__ "0|1|
S4cS4Q8A1M0S33S5Q40S12Vrho;S13VS;ZcA2A2A2A1S4bG0S33Voff;A1Vdata;A3A3").

Definition rl_new : list byte := ltac2:(tb__ "0|1|
S11S4Q8A1M0S21S4bG0SeG0S21A2S14Vrho;Vl0;A2A3A3").
Definition rl_rho' : valuation := ltac2:(tb__ "0|0|
S49S48Vrho;Vl;S24A3S18VS;A1S35S4Q8A1S21A2A3").
Definition rl_S' : sstate := ltac2:(tb__ "0|0|
S57VS;S56S15S1dVS;A1Vk;S1bVbase;Velo;Vehi;SfS1aA1S19Vl;A1A5A4A2").
Definition rl_md' (md : Model) : Model := ltac2:(tb__ "0|1|
S30S2fS27Vmd;A1S6Q40M0Z3A2S28Vp;S7G0S6G0Voff;A2S35S4Q8A1S21A2A3A2A3Vmd;A2").

Lemma rl_bs_len : ltac2:(tb__ "0|0|
S31S34SeS4Q8A1S21A2A1S5Q40S12Vrho;S13VS;ZcA2A2A2A2").
Proof using Hoff. clear Hll. unfold rl_bs. rewrite length_firstn. pose proof (bv_unsigned_in_range 64 (eval rho (reg_sv S 12))). lia. Qed.

Lemma rl_rho'_rw : ltac2:(tb__ "0|0|
S39S59R1S18VS;A1A2S0S4Q40A1S16S20R2A2S16Vrho;R2A2A3F_;Fi;").
Proof using Hoff. clear Hll. intros i Hi0. unfold rl_rho'. cbn. destruct (Pos.eqb_spec i (ss_next S)); [lia|]. reflexivity. Qed.
Lemma rl_rho'_nx : ltac2:(tb__ "0|0|
S0S4Q40A1S16S20S18VS;A1A2S35S4Q8A1S21A2A3").
Proof using . unfold rl_rho'. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma rl_rho'_rl : ltac2:(tb__ "0|0|
S39S3S0S39R1Vl;A3A1S0SaS4Q8A1A1S14S20R2A2S14Vrho;R2A2A3F_;Fi;").
Proof using . intros i Hi0. unfold rl_rho'. cbn. destruct (Pos.eqb_spec i l); [congruence|reflexivity]. Qed.
Lemma rl_rho'_l : ltac2:(tb__ "0|0|
S0SaS4Q8A1A1S14S20Vl;A2S24A3").
Proof using . unfold rl_rho'. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma rl_rho'_rm : ltac2:(tb__ "0|0|
S0S4Q40A1S8S4Q8A1A1F_;S1cS20A1S1cVrho;A1A3").
Proof using . reflexivity. Qed.

Lemma rl_writable : ltac2:(tb__ "0|2|
SaS29A1M0S3eS26S46Vsegs;Vrho;VS;SdG0S43R3S44R2R1A2A4A4S3S0S8SaS4Q8A1A1M1A1S2eS3fVsegs;R3A2S12Vrho;S13VS;ZbA2A2S12Vrho;S13VS;ZcA2A2A3S10G1A1A3A1F_;Fmd;Fms;Ftr;").
Proof using Hbuf Hhi Hnth.
  clear Hll. intros tr ms md Hsp.
  pose proof (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem segs _ _ _ _ _ Hsp) Hnth) as Ho.
  apply (writable_range_obj segs rho ms _ _ _ (soff rho elo) Ho eq_refl); [cbn [ob_base]; exact Hbuf | unfold obj_lo_of; cbn; lia | unfold obj_hi_of; cbn; exact Hhi].
Qed.

Lemma read_list_core : ltac2:(tb__ "0|c|
SaS29A1M0S3eS26S46Vsegs;Vrho;VS;SdG0S43R3S44R2R1A2A4A4S0S8S25A1M1S2aS27R2A1S6Q40M2Z3A2A2S9S25S28Vp;S6G2Voff;A2M3A2A2M4A3S0S8SaS4Q8A1M5A1M6A1M7S3bS2bR3A1Vp;A2S9G6Vdata;A2A3S2S4G2A1M8G8S2G6G6S1S0S8G8A1S41R7A1S9G8R2A2A3S1S0S3aS5G2R2A2Z3fA3S1S51R6A1S1S0G1S2aS27R6A1S4fS3dR7U0A2A1A2G4A3S1S0G7S2eS3fVsegs;R7A2S3dR7U1A2M9S3dR7U2A2MaA3S9G6R1A2A3S1S31S5G2GaA2MbS2cA2S1S31S32S5G2G9A2GbA2S2dA2S1S0G6S3cVdata;G3GaA3S21A3S1eVsegs;S20S22SdG0S43R8S44S54R7S35G5S21A2S42S40R7A1G9S21A3A3S23R6A1A2A4A4A2A2A2A2A2A2A2A2Lwdst;A2Lx8;A2F_;F_;F_;Fmd;Fms;Ftr;").
Proof using H10 H17 Hbuf Hcnt Hhi Hll Hnob Hnohi Hnolo Hnorl Hnth Hoff Hov.
  intros tr ms md Hsp Hfd Hfs.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  destruct (read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2)) as [wdst|] eqn:Ewd.
  2:{ exfalso. apply (rl_writable tr ms md Hsp). rewrite <- G1, <- G2. exact Ewd. }
  exists (Z_to_bv 64 63), wdst.
  assert (Hbs : file_read data (Z_to_bv 64 off) (ms_gpr ms 2) = rl_bs).
  { unfold rl_bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite G2. f_equal. f_equal. f_equal. apply Z_to_bv_small.
    rewrite two64. exact Hoff. }
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|]. split; [reflexivity|].
  split; [rewrite G2; lia|]. split; [rewrite G1, G2; exact Hov|]. split; [exact Hbs|].
  unfold rl_S', S_after_var, rl_rho'.
  assert (Hsp' : smatch_pending segs (rho_set_rl rho l rl_new) S (tr, mkCfg ms md)) by (apply smatch_pending_set_rl; [exact Hnorl | exact Hsp]).
  pose proof rl_bs_len as BL.
  eapply (smatch_after_kwrite_list segs (rho_set_rl rho l rl_new) S tr ms md tr _ (len_word rl_bs) k base elo ehi
            (soff rho elo) (soff rho ehi) l0 l (ms_gpr ms 1) rl_bs (soff rho elo) Hsp');
    [apply with_fds_idle; exact Hh | exact Hnth | apply soff_set_rl; exact Hnolo | apply soff_set_rl; exact Hnohi | | lia | lia |].
  - rewrite (eval_set_rl rho l rl_new base Hnob), G1. exact Hbuf.
  - rewrite rho_set_rl_at. cbn [rl rho_set_rl]. replace (Pos.eqb l0 l) with false by (symmetry; apply Pos.eqb_neq; congruence).
    rewrite Z.sub_diag. cbn [Z.to_nat firstn app]. unfold rl_new. reflexivity.
Qed.

Theorem triple1_read_listJ : ltac2:(tb__ "0|3|
S53OF_;S37S37S38Vsegs;R3R2A3S47Vsegs;R4R3A3SaS29A1M0S26R6Vrho;R2R1A3S1S0S8S25A1S2aS27R2A1S6Q40M1Z3A2A2S9S25S28Vp;S6G1Voff;A2A2A2A3S0S8SaS4Q8A1A1M2A1S3bS2bR2A1Vp;A2S9G2Vdata;A2A3A2F_;Fmd;Ftr;G0S26R7Vrho;R2R1A3R7S20R3S23R2A1A3F_;Fmd;Ftr;S52Vsegs;R7S36Vsegs;R6VS;Vrho;A4S36Vsegs;R5S22S20A4A4F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hbuf Hcnt Hhi Hi Hll Hnob Hnohi Hnolo Hnorl Hnth Hoff Hov.
  intros ok J J' Hokf Hokp HJfd HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_list_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_file_only_ok segs ms md x8 p (Z_to_bv 64 off) data wdst Hh H63 Hfd' Hfs Ewd Hc2 Hc3).
  - intros w' Hst.
    pose proof (@wstep_read_file_inv segs tr ms md x8 p (Z_to_bv 64 off) data wdst w' Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3 Hst) as ->.
    cbn zeta. rewrite Hbs. split; [exact Hsm'|].
    cbn [w_tr w_cfg cfg_model fst snd].
    replace (fd32 (ms_gpr ms 0)) with (Z_to_bv 64 3).
    2:{ pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0. rewrite G0, fd32_3. reflexivity. }
    apply HK. exact Hk.
Qed.

Theorem etriple_read_listJ : ltac2:(tb__ "0|3|
S37S37SaS29A1M0S26R4Vrho;R2R1A3S1S0S8S25A1S2aS27R2A1S6Q40M1Z3A2A2S9S25S28Vp;S6G1Voff;A2A2A2A3S0S8SaS4Q8A1A1M2A1S3bS2bR2A1Vp;A2S9G2Vdata;A2A3A2F_;Fmd;Ftr;G0S26R5Vrho;R2R1A3R5S20R3S23R2A1A3F_;Fmd;Ftr;S50Vsegs;S36Vsegs;R4VS;Vrho;A4S36Vsegs;R3S22S20A4A3F_;F_;FJ';FJ;").
Proof using H10 H17 Hbuf Hcnt Hhi Hi Hll Hnob Hnohi Hnolo Hnorl Hnth Hoff Hov.
  intros J J' HJfd HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_list_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & Hsm').
  eexists. split; [exact (@wstep_read_file_intro segs tr ms md x8 p (Z_to_bv 64 off) data wdst Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3)|].
  cbn zeta. rewrite Hbs. split; [exact Hsm'|].
  cbn [w_tr w_cfg cfg_model fst snd].
  replace (fd32 (ms_gpr ms 0)) with (Z_to_bv 64 3).
  2:{ pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0. rewrite G0, fd32_3. reflexivity. }
  apply HK. exact Hk.
Qed.
End ReadList.
End WithSegs.
