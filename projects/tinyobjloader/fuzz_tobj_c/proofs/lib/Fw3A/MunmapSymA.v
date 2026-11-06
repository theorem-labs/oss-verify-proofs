(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "reg_sv"; "SLit"; "rm"; "sobj"; "valuation"; "obj_range"; "ranges_disjoint"; "ss_next"; "ss_objs"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "shadow_addr"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "pair"; "list"; "bool"; "prod"; "true"; "Some"; "fst"; "option"; "snd"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "event"; "TASK_SIZE"; "map_has"; "map_remove"; "page_size"; "region_free"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "mmap_n"; "mmap_nZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundL SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA MmapFixedA MmapFixedA2 MmapNodesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section N.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

Lemma munmap_len_sym : ltac2:(tb__ "0|6|
S9S1eS11Q40M0A1M1A1S14S1eS2aA1M2S39S29S3S12S40Vsegs;R8R7R6S1dG2S3bR5S3cR4R3A2A4A5S0S3S5S13R7A1ZbA2R3A3S0G1S4RaR4A2S10G0R3A2A3S0S12S1bR4Z1000A2Z0M3A3S1S19G3R5A2S19R5S1cZ2Z3eA2A2A2S1S2S0G1S3aR9U1A2M4S10G0G3A2A3A1S1S0S12S45G4A1R6A3S1S0G1S44G4A1S10G0R6A2M5A3S0S12SfG0G5A2R6A3A2A2A2F_;F_;F_;F_;F_;Fnlit;Fen;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md en nlit Hsp H11 Een Hmod Hn.
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (_ & G1 & _). rewrite H11, Een in G1.
  assert (Un : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit) by (rewrite G1; exact Un).
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  split; [intros E; rewrite E in Hlenv; rewrite Z_to_bv_unsigned in Hlenv; change (bv_wrap 64 0) with 0 in Hlenv; lia|].
  split; [exact HnZ|]. split; [unfold mmap_n; rewrite HnZ; reflexivity | exact Un].
Qed.

Theorem triple1_munmap_symA : ltac2:(tb__ "0|f|
S3dOF_;S36S36S14S9S1eS11Q40M0A1M1A1S3S3S12S38Vsegs;R9R8A3S42Vsegs;RaR9A3S37Vsegs;ScS13R8A1A1RaA3S0S24S30A1S46Vsegs;SeS13R9A1A1A2S22S30S31A2A3S0S3S5S13RaA1Z11A2S6Zd7A1A3S0S3S5S13RbA1ZaA2R8A3S0S3S5S13RcA1ZbA2R8A3S0G1S4RcR9A2S10G0R8A2A3S0S12S1bR9Z1000A2Z0M2A3S1S19G2RaA2S19RaS1cZ2Z3eA2A2A2S1eS2aA1M3S39S29S40Vsegs;R12R11R13S1dG3S3bR3S3cR2R1A2A4A5R16R13R12R4R2A4S3aR4U0A2G1S1S0S12S1bSfG0R1A2M4S2eA2G2A3S1S1aS18G4R11A2M5S2bA2S1S0S1fS2cS28S27R4A1A1M6R1S10G0R11A2M7A3S21A3S1G1S26S20G1G1A2S1dG1G1R2R1A4S28S27R5A1A1A3S0G1R2S10G0R13A2A3F_;Fs;S1S0S1fS2fS2dG6R1A2R1G7A3S21A3S1S8S26S8R1SdS13R17A1A1A3SbSaR17R2A2S1dS12S12SfG0R3A2M8S18G8R13A2A4A2F_;Fo;S1S20S3S3A2M9S12S26G9R2S15R18A1A3S1S1aSfG0S4R18S23S3S3R3A3A2A2MaR2A2S19R2S18GaSfG0S4R18S25S3S3R3A3A2A2A2A2A2S2S1S1aSfG0R5A2MbSfG0S17SfG0S4R19S16R1aA1A2A2R3A2A2McA2S19GcS18GbR15A2A2A2A1F_;F_;Fy;Frr;R17S33R15S32S7R15A1R1G7A3A2S34G4G5R14A3R6S43R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;S3fVsegs;R14S35Vsegs;R13R11R10RfA5S3dS35Vsegs;R13S41R12S6G2A1A2S33R11S32S7R11A1S4R11RfA2MdS10G0RdA2A3A2S34SfG0GdA2MeS18GeRdA2R10A3R1A6Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fen;Fea;Ftp;Frho;FA;FJo;FJ;Fok;").
Proof using .
  intros ok J Jo A rho tp ea en nlit Hokf Hokp Hst Hi H17 H10 H11 Een Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (munmap_len_sym rho tp A tr ms md en nlit Hsp H11 Een Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite H10 in G0.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hhas & Huniq & Hfree & Hdisj & Hxs & HJo).
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE) by (rewrite HnZ; exact Hwrap).
  unfold TASK_SIZE in Hwrap.
  rewrite <- HnE in Hhas.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. apply (munmap_only_okA segs ms md _ H215 Hal Hlen Hwrap' Hhas).
  - intros w' Hw. rewrite (wstep_munmap_invA segs ms md _ Hh H215 Hal Hlen Hwrap' Hhas tr w' Hp Hw). rewrite HnE. rewrite <- G0.
    split.
    + unfold munmap_model, with_mmap_destroyed. unfold A_after.
      replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
      eapply (smatchA_after_munmap segs rho _ tp A tr ms md tr (munmap_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
                (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp);
        try reflexivity.
      all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
           try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
           try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
           try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
    + cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Theorem etriple_munmap_symA : ltac2:(tb__ "0|f|
S36S36S14S9S1eS11Q40M0A1M1A1S3S3S12S37Vsegs;ScS13R6A1A1R8A3S0S24S30A1S46Vsegs;SeS13R7A1A1A2S22S30S31A2A3S0S3S5S13R8A1Z11A2S6Zd7A1A3S0S3S5S13R9A1ZaA2R6A3S0S3S5S13RaA1ZbA2R6A3S0G1S4RaR7A2S10G0R6A2A3S0S12S1bR7Z1000A2Z0M2A3S1S19G2R8A2S19R8S1cZ2Z3eA2A2A2S1eS2aA1M3S39S29S40Vsegs;R10RfR11S1dG3S3bR3S3cR2R1A2A4A5R14R11R10R4R2A4S3aR4U0A2G1S1S0S12S1bSfG0R1A2M4S2eA2G2A3S1S1aS18G4RfA2M5S2bA2S1S0S1fS2cS28S27R4A1A1M6R1S10G0RfA2M7A3S21A3S1G1S26S20G1G1A2S1dG1G1R2R1A4S28S27R5A1A1A3S0G1R2S10G0R11A2A3F_;Fs;S1S0S1fS2fS2dG6R1A2R1G7A3S21A3S1S8S26S8R1SdS13R15A1A1A3SbSaR15R2A2S1dS12S12SfG0R3A2M8S18G8R11A2A4A2F_;Fo;S1S20S3S3A2M9S12S26G9R2S15R16A1A3S1S1aSfG0S4R16S23S3S3R3A3A2A2MaR2A2S19R2S18GaSfG0S4R16S25S3S3R3A3A2A2A2A2A2S2S1S1aSfG0R5A2MbSfG0S17SfG0S4R17S16R18A1A2A2R3A2A2McA2S19GcS18GbR13A2A2A2A1F_;F_;Fy;Frr;R15S33R13S32S7R13A1R1G7A3A2S34G4G5R12A3R6S43R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;S3eVsegs;S35Vsegs;R11RfReRdA5S3dS35Vsegs;R11S41R10S6G2A1A2S33RfS32S7RfA1S4RfRdA2MdS10G0RbA2A3A2S34SfG0GdA2MeS18GeRbA2ReA3R1A6Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fen;Fea;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp ea en nlit Hst Hi H17 H10 H11 Een Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (munmap_len_sym rho tp A tr ms md en nlit Hsp H11 Een Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite H10 in G0.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hhas & Huniq & Hfree & Hdisj & Hxs & HJo).
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE) by (rewrite HnZ; exact Hwrap).
  unfold TASK_SIZE in Hwrap.
  rewrite <- HnE in Hhas.
  eexists. split; [exact (wstep_munmap_introA segs ms md _ Hh H215 Hal Hlen Hwrap' Hhas tr Hp)|].
  rewrite HnE. rewrite <- G0. split.
  - unfold munmap_model, with_mmap_destroyed. unfold A_after.
    replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
    eapply (smatchA_after_munmap segs rho _ tp A tr ms md tr (munmap_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
              (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp);
      try reflexivity.
    all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
         try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
         try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
         try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

End N.
