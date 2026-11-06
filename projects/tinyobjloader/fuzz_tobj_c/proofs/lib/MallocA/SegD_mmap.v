(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "ss_next"; "SLit"; "reg_sv"; "rm"; "sobj"; "ss_objs"; "SVar"; "obj_range"; "ranges_disjoint"; "ss_pc"; "valuation"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "find_segment"; "machine_state"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "option"; "pair"; "None"; "Some"; "fst"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_add_lazy"; "with_vmmaps"; "event"; "ENOMEM"; "errno_ret"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "mmap_modeled_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_rw_vm"; "mmap_place_ok"; "mmap_n"; "mmap_rw_model"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA CompleteA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.

Lemma mmap_rw_model_lazy : ltac2:(tb__ "0|1|
S14Q40A1M0S33G0G0S1S24S41R4A1S25A3S1S33S49R5R4R3R2A4S35R2S48R3A1S36S46S34R4A1R3R2A3R4A2A3A3F_;Fa;Flen;Fm;Fflags;").
Proof. intros flags m len a H. unfold mmap_rw_model, with_mmap_backing. rewrite H. reflexivity. Qed.

Theorem triple1_mmap_lazyA : ltac2:(tb__ "0|10|
S43OF_;S2fS2fS14Q40M0A1M1S2fF_;S19S11S26G1A1S1eS31Vsegs;R8R7A3S4fVsegs;R9R8A3S30Vsegs;S7S15R6A1A1R9A3S1S27S3aA1S4cVsegs;S10S15R7A1A1A2S2aS3aS3bA2A3S1S5S9S15R8A1Z11A2S8ZdeA1A3S1S5S9S15R9A1ZbA2S8R6A1A3S1S1eS22R7Z1000A2Z0M2A3S0S1fG2R8A2S1fR8S23Z2Z3eA2A2A2S26S37A1M3S1dS33S4dVsegs;ReRdRfS28G3S4aR3S4bR2R1A2A4A5R13RfReR4R2A4S0S1S24S42S1bR4U2A2S1bR4U3M4A2M5S1bR4U5A2A3S25A3S0S1S24S41G5A1S25A3S0R13R10RfR5R3A4G1S47S1bR5U0A2S1bR5G4A2R4S1bR5U1M6A2R1A5S0SbS40SbR1ScS15R14A1A1A3SfSeR14R2A2S28S1eS1eS12G0R4A2M7S20G7R12A2A4A2F_;Fo;S0S1eS0S21S12G0R3A2M8R1A2S1fR1S20G8R11A2A2A2S1S27S32A1S1cVsegs;R2Z1A3S29S32A1A3F_;Fz;S0S2cS5S5A2M9S1eS40G9R2S16R15A1A3S0S21S12G0S6R15S2bS5S5R3A3A2A2MaR2A2S1fR2S20GaS12G0S6R15S2dS5S5R3A3A2A2A2A2A2S3S0S21S12G0R6A2MbS12G0S1aS12G0S6R16S17R17A1A2A2R3A2A2McA2S1fGcS20GbR14A2A2A2A1F_;F_;Fy;Fr;R14R2S3eS3dR12S3cSaR12A1R2S13G0R10A2MdA3A2S7S15R13A1A1R2A3R11R7S35R2GdS36S46S34R5A1S1bR6G6A2R2A3R5A2A3A5A2A2A2F_;Fa;A2A2A2F_;F_;Fmd;Fms;Ftr;S45Vsegs;R11S2eVsegs;R10RdRcRbA5S43S4S2eVsegs;R10S4eReS8S12G0S39S38A1A2A1A2RdRcR1A6S2G1G1S2eVsegs;R10R1A1S18RfS3fS15RfA1MeSdS7GeA1MfA1ScGeA1S50GfA1A4A2S3eS3dReS3cSaReA1R1S13G0RcA2A3A2GfR1A3RdR2A6La;A2A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Ftp;Frho;FA;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo A rho tp nlit Hokf Hokp Hst Hi H17 H11 Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit segs rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hn1 : mmap_n (ms_gpr ms 1) = Z_to_bv 64 nlit) by (unfold mmap_n; rewrite HnZ; reflexivity).
  assert (Hnl : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (apply u64_lit; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. apply (mmap_only_okA segs ms md _ Hh H222 Hlen Hmodb).
  - intros w' Hw. destruct (wstep_mmap_invA segs ms md _ Hh H222 Hlen Hmodb tr w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hseg & Hxs & HJo).
      pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).     rewrite HnZ in Pceil. rewrite Hn1 in Pfree.
      split.
      * rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1.
        eapply (smatchA_after_grant_lazy segs rho _ tp A tr ms md tr (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) a (Z_to_bv 64 nlit) a
                  (SVar (ss_next (ax_S A))) (Pos.succ (ss_next (ax_S A))) Hsp);
          rewrite ?Hnl; try reflexivity.
        -- unfold mmap_rw_vm. rewrite Hn1. reflexivity.
        -- exact Pal.
        -- change page_size with 4096. exact Hmod.
        -- lia.
        -- pose proof (alloc_top_lt (m_vmmaps md)). unfold two_pow_64 in *. lia.
        -- exact (region_free_app_r _ _ _ _ Pfree).
        -- exact Hseg.
        -- exact Hdisj.
        -- exact Hxs.
        -- apply agree_below_set_rw. lia.
        -- apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
        -- cbn. rewrite Pos.ltb_lt. apply Pos.lt_succ_diag_r.
        -- cbn [eval]. apply rho_set_rw_at.
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1. exact HJo.
Qed.

Theorem etriple_mmap_lazyA : ltac2:(tb__ "0|10|
S2fS14Q40M0A1M1S2fF_;S19S11S26G1A1S1eS30Vsegs;S7S15R4A1A1R6A3S1S27S3aA1S4cVsegs;S10S15R5A1A1A2S2aS3aS3bA2A3S1S5S9S15R6A1Z11A2S8ZdeA1A3S1S5S9S15R7A1ZbA2S8R4A1A3S1S1eS22R5Z1000A2Z0M2A3S0S1fG2R6A2S1fR6S23Z2Z3eA2A2A2S26S37A1M3S1dS33S4dVsegs;RcRbRdS28G3S4aR3S4bR2R1A2A4A5R10RdRcR4R2A4S0S1S24S42S1bR4U2A2S1bR4U3M4A2M5S1bR4U5A2A3S25A3S0S1S24S41G5A1S25A3S2G1G1S0S47S1bR5U0A2S1bR5G4A2R4S1bR5U1A2M6R1A5S0SbS40SbR1ScS15R11A1A1A3SfSeR11R2A2S28S1eS1eS12G0R3A2M7S20G7RfA2A4A2F_;Fo;S0S1eS0S21S12G0R2A2M8R1A2S1fR1S20G8ReA2A2A2S1S27S32A1S1cVsegs;R2Z1A3S29S32A1A3F_;Fz;S0S2cS5S5A2M9S1eS40G9R2S16R12A1A3S0S21S12G0S6R12S2bS5S5R3A3A2A2MaR2A2S1fR2S20GaS12G0S6R12S2dS5S5R3A3A2A2A2A2A2S3S0S21S12G0R5A2MbS12G0S1aS12G0S6R13S17R14A1A2A2R3A2A2McA2S1fGcS20GbR11A2A2A2A1F_;F_;Fy;Fr;R11R1S3eS3dRfS3cSaRfA1R1S13G0RdA2MdA3A2S7S15R10A1A1R1A3ReR6S35R1GdS36S46S34R4A1G6R1A3R4A2A3A5A2A2A2A2La;A2A2A2F_;F_;Fmd;Fms;Ftr;S44Vsegs;S2eVsegs;RdRbRaR9A5S43S2G1G1S2eVsegs;ReR1A1S18RdS3fS15RdA1MeSdS7GeA1MfA1ScGeA1S50GfA1A4A2S3eS3dRcS3cSaRcA1R1S13G0RaA2A3A2GfR1A3RbR2A6La;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;Fnlit;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp nlit Hst Hi H17 H11 Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit segs rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & a & Hpl & Hdisj & Hseg & Hxs & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hn1 : mmap_n (ms_gpr ms 1) = Z_to_bv 64 nlit) by (unfold mmap_n; rewrite HnZ; reflexivity).
  assert (Hnl : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (apply u64_lit; lia).
  eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
  exists a. pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).     rewrite HnZ in Pceil. rewrite Hn1 in Pfree.
  split.
  - rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1.
    eapply (smatchA_after_grant_lazy segs rho _ tp A tr ms md tr (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) a (Z_to_bv 64 nlit) a
              (SVar (ss_next (ax_S A))) (Pos.succ (ss_next (ax_S A))) Hsp);
      rewrite ?Hnl; try reflexivity.
    + unfold mmap_rw_vm. rewrite Hn1. reflexivity.
    + exact Pal.
    + change page_size with 4096. exact Hmod.
    + lia.
    + pose proof (alloc_top_lt (m_vmmaps md)). unfold two_pow_64 in *. lia.
    + exact (region_free_app_r _ _ _ _ Pfree).
    + exact Hseg.
    + exact Hdisj.
    + exact Hxs.
    + apply agree_below_set_rw. lia.
    + apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
    + cbn. rewrite Pos.ltb_lt. apply Pos.lt_succ_diag_r.
    + cbn [eval]. apply rho_set_rw_at.
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1. exact HJo.
Qed.

End M.
