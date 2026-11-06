(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "reg_sv"; "sobj"; "eval"; "ss_next"; "SLit"; "sstate"; "valuation"; "ss_objs"; "sv"; "rm"; "ss_pc"; "obj_range"; "ranges_disjoint"; "ro_addr"; "SVar"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "true"; "list"; "option"; "false"; "Some"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_n"; "mmap_place_ok"; "mmap_rw_vm"; "munmap_model"; "mmap_fixed_dead_model"; "mmap_fixed_ok_model"; "mmap_none_vm"; "mmap_place_ok_none"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "page_size"; "map_contains"; "vm_maps"; "with_vmmaps"; "vm_brk"; "TASK_SIZE"; "alloc_top"; "map_has"; "region_free"; "two_pow_64"; "vm_noaccess"; "VmMaps"; "vm_reserved"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "rho_set_rw"; "ok_pframeJ"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple1"; "etriple"; "model_idle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.Heap"; "S_ret_lit"; "S_ret_fresh"; "enomem_ret"; "rho_after_zero"; "rho_after_unmap"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "zero_range"; "after_sys_mem"; "after_sys"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noaccess_b"; "brk_grow_ok"; "brk_model_next"; "mmap_fixed_noaccess_b"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundR
  SymFrame SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Heap.
Variable segs : list Segment.

Lemma smatch_pending_reunmap : ltac2:(tb__ "0|4|
S12S11S22S3aA1M0S6S39S9Q40M1A1M2G2S4aVsegs;R7R6S20G0S37R5S38R4R3A2A4A4S33S32S8G1R3A2S8G1R2A2A2S36Z2Z40A2A2SdS5aSdR1S13R9A1A3S18S17RbR2A2S20S26S26S8G1R6A2M3S32G3S8G1R5A2A2A4A2F_;Fo;S4aVsegs;S52RaS5bS15RaA1R5R4A3A2R9S20G0S37R8S38S53R7S5bS7R7A1R5R4A3A2R6A2A4A4F_;F_;F_;Fn;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md a n Hsp Hnw Hdisj.
  pose proof Hsp as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (swf_objs S Hwf) as Hobjwf.
  assert (Hur : forall mem x, unmap_range mem a n x = if in_range a n x then None else mem x)
    by (intros; apply unmap_range_at).
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split; [cbn; rewrite eval_set_rm; exact Hpend|].
  split; [exact Hhalt|]. split; [exact Hrom|].
  split.
  { intros x Hro. cbn [with_mem ms_mem]. rewrite Hur. destruct (in_range a n x); [reflexivity|].
    apply Hroc. exact Hro. }
  split; [intros r Hr; rewrite eval_set_rm; apply Hregs; exact Hr|].
  split; [intros r; rewrite eval_set_rm; apply Hfregs|].
  split; [unfold fcsr_match in *; destruct (ss_fcsr S); [exact Hfcsr | rewrite eval_set_rm; exact Hfcsr]|].
  split; [unfold resv_match in *; cbn [with_mem ms_resv]; destruct (ss_resv S); destruct (ms_resv ms);
          rewrite ?eval_set_rm; exact Hresv|].
  split; [|apply Forall_forall; intros p Hp; apply holds_set_rm; exact (proj1 (Forall_forall _ _) Hfacts p Hp)].
  split; [|split].
  - apply Forall_forall. intros o Hin.
    pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Ho.
    pose proof (proj1 (forallb_forall _ _) Hobjwf o Hin) as Howf.
    eapply (obj_holds_set_rm_ext segs rho _ ms); [intros ?; reflexivity | | exact Ho].
    intros off Hoff. cbn [with_mem ms_mem]. rewrite Hur.
    pose proof (Hdisj o Hin) as D. pose proof (proj1 Ho) as HB.
    unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D.
    destruct (in_range a n _) eqn:Hir; [|reflexivity].
    apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
  - apply pairwise_disjoint_set_rm. exact Hpd.
  - intros x Hout. apply outside_all_set_rm in Hout. cbn [with_mem ms_mem set_rm rm]. rewrite !Hur.
    destruct (in_range a n x); [reflexivity|]. apply Hfr. exact Hout.
Qed.

Lemma after_sys_mem_with_mem : ltac2:(tb__ "0|1|
S6S9Q40A1M0G0S23S9Q8A1A1F_;S0S6S5dR3R2R1A3S5eS53R3R1A2R2A2A3Fmem;Fr;Fms;").
Proof using . intros. reflexivity. Qed.

Lemma smatch_after_mem_ret : ltac2:(tb__ "0|4|
S12S11S22S3aA1M0S6S39G0S39S9Q40A1M1G1S23S9Q8A1A1F_;M2G2S4aVsegs;S52RaR1A2R9S20G0S37R8S38S53R7R2A2R6A2A4A4S51R5A1S1bVsegs;S4bS52RcR3A2SfRbA1M3R5A3S4dRbS1aG3A1S13RbA1S66G3A1A4S20G0S37R7S38S5dR9R5R4A3R6A2A4A4F_;F_;Fm;Fmem;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r mem m Hsp Hh'.
  rewrite after_sys_mem_with_mem. exact (smatch_after_ret segs _ S tr _ md tr' md' r Hsp Hh').
Qed.

Lemma smatch_after_mem_lit : ltac2:(tb__ "0|4|
S12S11S22S3aA1M0S6S39G0S39S9Q40M1A1M2G2S23S9Q8A1A1F_;M3G3S4aVsegs;S52RaR1A2R9S20G0S37R8S38S53R7R2A2R6A2A4A4S51R5A1S1bVsegs;S52RcR3A2S4dRbS10S8G1R5A2A1S13RbA1SfRbA1A4S20G0S37R7S38S5dR9R5R4A3R6A2A4A4F_;F_;Fm;Fmem;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r mem m Hsp Hh'.
  rewrite after_sys_mem_with_mem. exact (smatch_after_ret_lit segs _ S tr _ md tr' md' r Hsp Hh').
Qed.

Lemma pending_args : ltac2:(tb__ "0|2|
S12S11S22S3aA1M0S6S39S4aVsegs;R5R4S20G0S37R3S38R2R1A2A4A4S1S0S9Q40A1M1S5R3U0A2SeR6ScR5ZaA2A2A3S1S0G1S5R3U1A2SeR6ScR5ZbA2A2A3S1S0G1S5R3U2A2SeR6ScR5ZcA2A2A3S1S0G1S5R3U3A2SeR6ScR5ZdA2A2A3S1S0G1S5R3U4A2SeR6ScR5ZeA2A2A3S0G1S5R3U5A2SeR6ScR5ZfA2A2A3A2A2A2A2A2F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsp.
  repeat split;
  [ exact (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 3 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 4 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 5 Hsp ltac:(lia)) ].
Qed.

Lemma mmap_nw : ltac2:(tb__ "0|3|
S47S9Q40M0A1M1G1S33S32S8G0R2A2S29R1A1A2S42R3A1A2S1S0S26S8G0S2aR2A1A2M2S29R2A1A3S33S32S8G0R3A2G2A2S36Z2Z40A2A2A2F_;Flen;Fa;Fh;").
Proof using .
  intros h a len H. pose proof (urange a) as Ha.
  assert (Hn : 0 <= mmap_nZ len).
  { unfold mmap_nZ, page_round_up_Z, page_size. pose proof (urange len). apply Z.mul_nonneg_nonneg; [|lia]. apply Z.div_pos; lia. }
  assert (Hc : alloc_top h < 2 ^ 64) by (pose proof (alloc_top_lt h); unfold two_pow_64 in *; lia).
  assert (E : bv_unsigned (mmap_n len) = mmap_nZ len).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. lia. }
  rewrite E. lia.
Qed.

Definition rho_after_zero (rho : valuation) (nx : positive) (r a n : word) : valuation := ltac2:(tb__ "0|0|
S4bS52Vrho;S5cS15Vrho;A1Va;Vn;A3A2Vnx;Vr;A3").

Definition rho_after_unmap (rho : valuation) (nx : positive) (r a n : word) : valuation := ltac2:(tb__ "0|0|
S4bS52Vrho;S5bS15Vrho;A1Va;Vn;A3A2Vnx;Vr;A3").

Definition S_ret_fresh (S : sstate) : sstate := ltac2:(tb__ "0|1|
S4dVS;S1aSfVS;A1M0A1S13VS;A1S66G0A1A4").
Definition S_ret_lit (S : sstate) (z : Z) : sstate := ltac2:(tb__ "0|0|
S4dVS;S10Vz;A1S13VS;A1SfVS;A1A4").

Definition enomem_ret : Z := bv_unsigned (errno_ret ENOMEM).

Theorem triple1_mmap_rwJ : ltac2:(tb__ "0|a|
S4eOF_;S1dS1dS9Q40M0A1M1S1dF_;S11S12S1eVsegs;R6R5A3S4cVsegs;R7R6A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10ZdeA1A3S22S3aA1M2S6S39S4aVsegs;R8R9S20G2S37R3S38R2R1A2A4A4RdR9R4R2A3S1S2S0G1S5R4U1M3A2SaG0Z0A2A3A1S1S0S1fS5fS5R4U2A2S5R4U3M4A2M5S5R4U5A2A3S21A3S1S0S1fS60G5A1S24A3S1RdRaR5R3A3G1S2bS5R5U0A2S5R5G4A2R4S5R5G3A2R1A5S1SdS5aSdR1S13ReA1A3S18S17ReR2A2S20S26S26S8G0R4A2M6S32G6S29S5R8G3A2A1A2A4A2F_;Fo;S1G1S1S33S8G0R3A2M7S8G0R1A2M8A2S34G8S32G7S29S5R7G3A2A1A2A2A2S0S1fS19Vsegs;R2A2S24A3F_;Fx;ReR2S58RcSfRdA1R2R2S2aS5R6G3A2M9A1A5R7S3fS2cS3bR5A1G9R2A3R5A2A4A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RbS1cVsegs;RaR7R6A4S4eS4S1cVsegs;RaS55R8S57A2R7R1A5S3G1G1S1cVsegs;RaR1A1S56R9A1S58R8SfR9A1R1R1S2aSeR8ScR9ZbA2A2A1A5R2A5La;A2A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hmod & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@mmap_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_inv Hp Hh H222 Hlen Hmod Hnr Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
      split.
      * unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
        eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
        apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

Theorem etriple_mmap_rw_okJ : ltac2:(tb__ "0|a|
S1dS9Q40M0A1M1S1dF_;S11S12S0S23S27A1S54Vsegs;S16R2A1A2S25S27S28A2A3S0S14ScR3Z11A2S10ZdeA1A3S22S3aA1M2S6S39S4aVsegs;R6R7S20G2S37R3S38R2R1A2A4A4RaR7R4R2A3S1S2S0G1S5R4U1M3A2SaG0Z0A2A3A1S1S0S1fS5fS5R4U2A2S5R4U3M4A2M5S5R4U5A2A3S21A3S1S0S1fS60G5A1S24A3S3G1G1S1S2bS5R5U0A2S5R5G4A2R4S5R5G3A2M6R1A5S1SdS5aSdR1S13RbA1A3S18S17RbR2A2S20S26S26S8G0R3A2M7S32G7S29S5R7G3A2A1A2A4A2F_;Fo;S1G1S1S33S8G0R2A2M8S8G0R1A2M9A2S34G9S32G8S29S5R6G3A2A1A2A2A2S0S1fS19Vsegs;R2A2S24A3F_;Fx;RbR1S58R9SfRaA1R1R1S2aG6A1A5R6S3fS2cS3bR4A1G6R1A3R4A2A4A2A2A2La;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S50Vsegs;S1cVsegs;R7R5R4A4S4eS3G1G1S1cVsegs;R8R1A1S56R7A1S58R6SfR7A1R1R1S2aSeR6ScR7ZbA2A2A1A5R2A5La;A2Lw;A3F_;F_;F_;Frho;FS;FJo;FJ;").
Proof using .
  intros J Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hmod & Hnr & a & Hpl & Hdisj & Hnro & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
  eexists. split; [eapply (@wstep_mmap_intro_ok segs tr ms); eassumption|].
  exists a. split.
  - unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
    eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
    apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

Theorem etriple_mmap_rw_failJ : ltac2:(tb__ "0|4|
S1dS1dS11S12S0S23S27A1S54Vsegs;S16R2A1A2S25S27S28A2A3S0S14ScR3Z11A2S10ZdeA1A3S22S3aA1M0S6S39S4aVsegs;R6R7S20G0S37R3S38R2R1A2A4A4RaR7R4R2A3S1S2S0S9Q40M1A1S5R4U1A2M2SaG1Z0A2A3A1S1S0S1fS5fS5R4U2A2S5R4U3A2M3S5R4U5A2A3S21A3S1S0S1fS61G3R3S29G2A1A3S21A3RaR8R5R3A3A2A2A2F_;F_;Fmd;Fms;Ftr;S50Vsegs;S1cVsegs;R7R5R4A4S1cVsegs;R6S55R5S57A2R4A4A3F_;F_;F_;Frho;FS;FJf;FJ;").
Proof using .
  intros J Jf S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hmod & Hrf & HJf).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  eexists. split; [eapply (@wstep_mmap_intro_fail segs tr ms); eassumption|].
  split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem etriple_mmap_rw_anyJ : ltac2:(tb__ "0|b|
S1dS1dS9Q40M0A1M1S1dF_;S11S12S0S23S27A1S54Vsegs;S16R2A1A2S25S27S28A2A3S0S14ScR3Z11A2S10ZdeA1A3S22S3aA1M2S6S39S4aVsegs;R6R7S20G2S37R3S38R2R1A2A4A4RbR7R4R2A3S1S2S0G1S5R4U1M3A2M4SaG0Z0A2A3A1S1S0S1fS5fS5R4U2A2S5R4U3M5A2M6S5R4U5A2A3S21A3S1S0S1fS60G6A1S24A3S1S0S1fS61G6R3S29G4A1A3S21A3RcR9R6R4A3F_;G1S2bS5R5U0A2S5R5G5A2R4S5R5G3A2R1A5S1SdS5aSdR1S13RcA1A3S18S17RcR2A2S20S26S26S8G0R4A2M7S32G7S29S5R8G3A2A1A2A4A2F_;Fo;S1G1S1S33S8G0R3A2M8S8G0R1A2M9A2S34G9S32G8S29S5R7G3A2A1A2A2A2S0S1fS19Vsegs;R2A2S24A3F_;Fx;RcR2S58RaSfRbA1R2R2S2aS5R6G3A2MaA1A5R7S3fS2cS3bR5A1GaR2A3R5A2A4A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S50Vsegs;S1cVsegs;R8R5R4A4S4eS4S1cVsegs;R8S55R6S57A2R5R1A5S3G1G1S1cVsegs;R8R1A1S56R7A1S58R6SfR7A1R1R1S2aSeR6ScR7ZbA2A2A1A5R2A5La;A2A2Lw;A3F_;F_;F_;Frho;FS;FJo;FJf;FJ;").
Proof using .
  intros J Jf Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hmod & Hnr & HJf & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_grant_refusable (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [eapply (@wstep_mmap_intro_fail segs tr ms); eassumption|].
    left. split; [|exact (HJf eq_refl)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
  - assert (Hpl' : exists a, mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a).
    { exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf). }
    destruct Hpl' as [a Hpl]. destruct (HJo a Hpl) as (Hdisj & Hnro & HJoa).
    pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
    eexists. split; [eapply (@wstep_mmap_intro_ok segs tr ms); eassumption|].
    right. exists a. split.
    + unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
      eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
      apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJoa.
Qed.

Theorem triple1_mmap_noneJ : ltac2:(tb__ "0|9|
S4eOF_;S1dS1dS9Q40M0A1M1S1dF_;S11S12S1eVsegs;R6R5A3S4cVsegs;R7R6A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10ZdeA1A3S22S3aA1M2S6S39S4aVsegs;R8R9S20G2S37R3S38R2R1A2A4A4RdR9R4R2A3S1S2S0G1S5R4U1M3A2SaG0Z0A2A3A1S1S0S1fS62S5R4U2A2M4S5R4U3A2M5S5R4U5A2M6A3S21A3S1S0S1fS5fG4G5G6A3S24A3S1S0S1fS60G5A1S24A3S1RdRaR5R3A3G1S31S5R5U0A2R4S5R5G3A2R1A4S1SdS5aSdR1S13ReA1A3S18S17ReR2A2S20S26S26S8G0R4A2M7S32G7S29S5R8G3A2A1A2A4A2F_;Fo;ReR2S59RcSfRdA1R2R2S2aS5R6G3A2M8A1A5R7S3fS30S3bR5A1G8R2A3R5A2A4A2F_;Fa;A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RbS1cVsegs;RaR7R6A4S4eS4S1cVsegs;RaS55R8S57A2R7R1A5S3G1G1S1cVsegs;RaR1A1S56R9A1S59R8SfR9A1R1R1S2aSeR8ScR9ZbA2A2A1A5R2A5La;A2A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hna & Hmod & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@mmap_none_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_none_inv Hp Hh H222 Hlen Hna Hmod Hnr Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
      split.
      * unfold S_ret_fresh, rho_after_unmap. rewrite <- G1.
        eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
        apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

Theorem triple1_munmapJ : ltac2:(tb__ "0|a|
S4eOF_;S1dS1dS11S12S1eVsegs;R5R4A3S4cVsegs;R6R5A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10Zd7A1A3S22S3aA1M0S6S39S4aVsegs;R8R9S20G0S37R3S38R2R1A2A4A4RcR9R4R2A3S1S0S26S35S8Q40M1S5R4U0M2A2M3A2M4S3cA2Z0M5A3S1S2S0S9G1A1S5R4U1M6A2M7SaG1G5A2A3A1S1S33S32G4S29G7A1A2S41A2S1S0S1fS43S3eS3bR3A1A1G3S2aG7A1M8A3S21A3S1SdS5aSdR1S13RcA1A3S18S17RcR2A2S20S26S26S8G1S5R6G2A2A2M9S32G9S29S5R6G6A2A1A2A4A2F_;Fo;RcS52RaS5bS15RaA1G3G8A3A2R5S2dR3G3G8A3A3A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RaS1cVsegs;R9R7R6A4S1cVsegs;R8S55R7G5A2S52R6S5bS15R6A1SeR6ScR7ZaA2A2S2aSeR6ScR7ZbA2A2A1A3A2A4A4F_;F_;F_;F_;F_;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hlen & Hwrap & Hhas & Hdisj & HJ').
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold TASK_SIZE in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@munmap_exact_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (@wstep_munmap_exact_inv segs ms md) in Hw; try eassumption. rewrite Hw.
    split.
    + unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
      eapply smatch_after_mem_lit; [| apply munmap_model_idle; exact Hh].
      apply smatch_pending_reunmap; [exact Hsp | unfold TASK_SIZE in Hwrap; lia | rewrite En; exact Hdisj].
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJ'.
Qed.

Theorem etriple_munmapJ : ltac2:(tb__ "0|a|
S1dS1dS11S12S0S23S27A1S54Vsegs;S16R2A1A2S25S27S28A2A3S0S14ScR3Z11A2S10Zd7A1A3S22S3aA1M0S6S39S4aVsegs;R6R7S20G0S37R3S38R2R1A2A4A4RaR7R4R2A3S1S0S26S35S8Q40M1S5R4U0M2A2M3A2M4S3cA2Z0M5A3S1S2S0S9G1A1S5R4U1M6A2M7SaG1G5A2A3A1S1S33S32G4S29G7A1A2S41A2S1S0S1fS43S3eS3bR3A1A1G3S2aG7A1M8A3S21A3S1SdS5aSdR1S13RaA1A3S18S17RaR2A2S20S26S26S8G1S5R6G2A2A2M9S32G9S29S5R6G6A2A1A2A4A2F_;Fo;RaS52R8S5bS15R8A1G3G8A3A2R5S2dR3G3G8A3A3A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S50Vsegs;S1cVsegs;R7R5R4A4S1cVsegs;R6S55R5G5A2S52R4S5bS15R4A1SeR4ScR5ZaA2A2S2aSeR4ScR5ZbA2A2A1A3A2A4A3F_;F_;F_;Frho;FS;FJ';FJ;").
Proof using .
  intros J J' S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hlen & Hwrap & Hhas & Hdisj & HJ').
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold TASK_SIZE in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  eexists. split; [eapply (@wstep_munmap_exact_intro segs ms md); eassumption|].
  split.
  - unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
    eapply smatch_after_mem_lit; [| apply munmap_model_idle; exact Hh].
    apply smatch_pending_reunmap; [exact Hsp | unfold TASK_SIZE in Hwrap; lia | rewrite En; exact Hdisj].
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJ'.
Qed.

Theorem triple1_brk_queryJ : ltac2:(tb__ "0|3|
S4eOF_;S1dS9Q40A1M0S1dF_;S11S12S1eVsegs;R5R4A3S4cVsegs;R6R5A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10Zd6A1A3S0S14ScR6ZaA2S10Z0A1A3S22S3aA1M1S6S39S4aVsegs;R9RaS20G1S37R3S38R2R1A2A4A4RdRaR4R2A3RdS40S3bR3A1A1M2S4bRbSfRcA1G2A3R5R3A4F_;F_;Fmd;Fms;Ftr;S4fVsegs;RbS1cVsegs;RaR8R7A4S4eS3G0G0S1cVsegs;RbR1A1S56RaA1S4bR9SfRaA1R1A3R2A5Lb;A2Lw;A4F_;F_;F_;F_;F_;F_;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 H10 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & _). rewrite H10 in G0. cbn [eval] in G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@brk_query_only_ok segs); eassumption.
  - intros w' Hw. eapply (@wstep_brk_query_inv segs) in Hw; try eassumption. rewrite Hw.
    exists (vm_brk (m_vmmaps md)). split.
    + unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
    + cbn [w_tr w_cfg fst snd cfg_model]. exact (HJ tr ms md Hsp Hk).
Qed.

Theorem etriple_brk_queryJ : ltac2:(tb__ "0|3|
S1dS9Q40A1M0S1dF_;S11S12S0S23S27A1S54Vsegs;S16R2A1A2S25S27S28A2A3S0S14ScR3Z11A2S10Zd6A1A3S0S14ScR4ZaA2S10Z0A1A3S22S3aA1M1S6S39S4aVsegs;R7R8S20G1S37R3S38R2R1A2A4A4RbR8R4R2A3RbS40S3bR3A1A1M2S4bR9SfRaA1G2A3R5R3A4F_;F_;Fmd;Fms;Ftr;S50Vsegs;S1cVsegs;R8R6R5A4S4eS3G0G0S1cVsegs;R9R1A1S56R8A1S4bR7SfR8A1R1A3R2A5Lb;A2Lw;A3F_;F_;F_;F_;Frho;FS;FJ';FJ;").
Proof using .
  intros J J' S rho Hi H17 H10 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & _). rewrite H10 in G0. cbn [eval] in G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  eexists. split; [eapply (@wstep_brk_query_intro segs tr ms); eassumption|].
  exists (vm_brk (m_vmmaps md)). split.
  - unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
  - cbn [w_tr w_cfg fst snd cfg_model]. exact (HJ tr ms md Hsp Hk).
Qed.

Theorem triple1_brk_growJ : ltac2:(tb__ "0|d|
S4eOF_;S1dS1dS1dS11S12S9Q40M0A1M1S1eVsegs;R7R6A3S4cVsegs;R8R7A3S0S23S27A1S54Vsegs;S16R5A1A2S25S27S28A2A3S0S14ScR6Z11A2S10Zd6A1A3S22S3aA1M2S6S39S4aVsegs;R9RaS20G2S37R3S38R2R1A2A4A4ReRaR4R2A3S1S0G1S40S3bR3A1M3A1RaA3S1S33S8G0S49G3A1A2S8G0RaA2M4A2S1S0S26S35G4S3cA2Z0M5A3S1S0S26S35S8G0S5R4U0M6A2M7A2M8S3cA2G5A3S1S1S34G5G4A2S34G4G8A2A2S1ReS4bRbSfRcA1RaA3R5R3A3S0S1fS63R3G7G7A3S21A3S1SdS5aSdR1S13ReA1A3S18S17ReR2A2S20S26S26S8G0RdA2S8G0S5R7G6A2A2A4A2F_;Fo;S1G1S1S33S8G0RcA2S8G0R1A2M9A2S34G9S8G0S5R6G6A2A2A2A2S0S1fS19Vsegs;R2A2S24A3F_;Fx;ReS52RcS5cS15RcA1RbSbG0S5R5G6A2MaRbA3A3A2R6S3fS64S3bR4A1GaGaA3R4A2A3A2A2F_;A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RcS1cVsegs;RbR8R7A4S4eS4S1cVsegs;RbS56R9A1S4bR8SfR9A1MbR7A3R1A5S1cVsegs;RaS4dR9ScR9ZaA2McS13R9A1GbA4S52R8S5cS15R8A1R7SbG0SeR8GcA2R7A3A3A2R1A5A2Lw;A4F_;F_;F_;F_;F_;Fb0;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho b0 Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hb0 & Hsb & Halo & Halr & Hlt & HJf & HOK). subst b0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@brk_grow_only_ok segs); try eassumption; lia.
  - intros w' Hw. eapply (@wstep_brk_grow_inv segs) in Hw; try eassumption; [|lia]. destruct Hw as [(Hg & ->) | ->].
    + right. destruct (HOK Hg) as (Hdisj & Hnro & HJo).
      rewrite (brk_eff_grow_aligned (m_vmmaps md) (ms_gpr ms 0) Halo Halr Hlt).
      change (eff_mem ms (mkEffect (ms_gpr ms 0) [] [(vm_brk (m_vmmaps md), (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv)]))
        with (zero_range (ms_mem ms) (vm_brk (m_vmmaps md)) (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv).
      pose proof (urange (ms_gpr ms 0)) as Hr0.
      assert (En : bv_unsigned (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv = bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps md))).
      { rewrite bv_sub_unsigned. apply bv_wrap_small. rewrite two64. lia. }
      split.
      * rewrite <- G0. rewrite after_sys_mem_with_mem.
        eapply smatch_after_ret_expr; [| split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)] | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
        apply smatch_pending_rezero; [exact Hsp | rewrite En; lia | rewrite En | rewrite En].
        -- intros o Ho. replace (bv_unsigned (vm_brk (m_vmmaps md)) + (bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps md)))) with (bv_unsigned (ms_gpr ms 0)) by lia. exact (Hdisj o Ho).
        -- intros x Hx. apply Hnro. lia.
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0. exact HJo.
    + left. split.
      * unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
      * cbn [w_tr w_cfg fst snd cfg_model]. exact HJf.
Qed.

Theorem triple1_mprotect_exposeJ : ltac2:(tb__ "0|10|
S4eOF_;S1dS1dS1dS11S12S1eVsegs;R6R5A3S4cVsegs;R7R6A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10Ze2A1A3S22S3aA1M0S6S39S4aVsegs;R8R9S20G0S37R3S38R2R1A2A4A4RdR9R4R2A3S1S0S26S8Q40M1S5R4U2A2A2Z3A3S1S0S26S35S8G1S5R4U0M2A2M3A2M4S3cA2Z0M5A3S1S2S0S9G1A1M6S5R4U1M7A2M8SaG1G5A2A3A1S1S34S32G4S29G8A1A2S45A2S1S0S1fS3dS46S3bR3A1M9A1G3S2aG8A1MaA3S21A3S1S0S1fS3dS3eG9A1G3GaA3S21A3S1RdRaR5R3A3S0S1fS67R3G3GaA3S21A3S1SdS5aSdR1S13RdA1A3S18S17RdR2A2S20S26S26S8G1S5R7G2A2A2MbS32GbS29S5R7G7A2A1A2A4A2F_;Fo;S1G6S1S33S8G1S5R6G2A2A2McS8G1R1A2MdA2S34GdS32GcS29S5R6G7A2A1A2A2A2S0S1fS19Vsegs;R2A2S24A3F_;Fx;RdS52RbS5cS15RbA1S5R5G2A2MeS2aS5R5G7A2A1MfA3A2R6S68R4GeGfA3A3A2A2F_;A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RbS1cVsegs;RaR7R6A4S4eS4S1cVsegs;RaS55R8S57A2R7R1A5S1cVsegs;R9S55R8G5A2S52R7S5cS15R7A1SeR7ScR8ZaA2A2S2aSeR7ScR8ZbA2A2A1A3A2R1A5A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hna & Hmp & HJf & HOK).
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold two_pow_64 in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@mprotect_expose_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (@wstep_mprotect_expose_inv segs ms md) in Hw; try eassumption. destruct Hw as [-> | (Hb & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. destruct (HOK Hb) as (Hdisj & Hnro & HJo). split.
      * unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
        eapply smatch_after_mem_lit; [| apply mprotect_model_next_idle; exact Hh].
        apply smatch_pending_rezero; [exact Hsp | unfold two_pow_64 in Hwrap; lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
Qed.

Theorem triple1_mprotect_noopJ : ltac2:(tb__ "0|9|
S4eOF_;S1dS1dS11S12S1eVsegs;R5R4A3S4cVsegs;R6R5A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10Ze2A1A3S22S3aA1M0S6S39S4aVsegs;R8R9S20G0S37R3S38R2R1A2A4A4RcR9R4R2A3S1S0S26S8Q40M1S5R4U2A2A2Z3A3S1S0S26S35S8G1S5R4U0A2M2A2M3S3cA2Z0M4A3S1S2S0S9G1A1S5R4U1A2M5SaG1G4A2A3A1S1S34S32G3S29G5A1A2S45A2S1S0S1fS3dS46S3bR3A1M6A1M7G2S2aG5A1M8A3S24A3S1S0S1fS3dS3eG6A1G2G8A3S21A3S1S0S1fS44G7G2G8A3S21A3RcRaR5R3A3A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RaS1cVsegs;R9R7R6A4S1cVsegs;R8S55R7G4A2R6A4A4F_;F_;F_;F_;F_;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hna & Hmp & Hrf & HJ').
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@mprotect_noop_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (@wstep_mprotect_noop_inv segs ms md) in Hw; try eassumption. rewrite Hw.
    split; [|exact HJ']. unfold S_ret_lit. change 0 with (bv_unsigned (Z_to_bv 64 0)).
    eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem triple1_mmap_fixedJ : ltac2:(tb__ "0|12|
S4eOF_;S1dS1dS1dS1dS11S12S1eVsegs;R7R6A3S4cVsegs;R8R7A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10ZdeA1A3S22S3aA1M0S6S39S4aVsegs;R8R9S20G0S37R3S38R2R1A2A4A4ReR9R4R2A3S1S2S0S9Q40M1A1S5R4U1M2A2M3SaG1Z0M4A2A3A1S1S0S1fS65S5R4U2A2M5S5R4U3A2M6S5R4U5A2M7A3S21A3S1S0S1fS62G5G6G7A3S24A3S1S0S1fS5fG5G6G7A3S24A3S1S33S32S8G1S5R4U0M8A2M9A2MaS29G3A1A2S42S3bR3A1MbA1A2S1S0S26S35GaS3cA2G4A3S1S34G4GaA2S1S0S1fS44S48GbA1G9S2aG3A1McA3S21A3S1S0S1fS3dS3eGbA1G9GcA3S21A3S1S0S1fS60G6A1S24A3S1SdS5aSdR1S13RcA1A3S18S17RcR2A2S20S26S26S8G1S5R6G8A2A2MdS32GdS29S5R6G2A2A1A2A4A2F_;Fo;S1ReRaR5R3A3S1RdS52RaS5bS15RaA1G9GcA3A2MeR5S2fG6R3G9GcA4A3RcGeR5S2eR3G9GcA3A3A2A2A2A2A2A2A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RcS1cVsegs;RbR7R6A4S4eS4S1cVsegs;RbS55R8S57A2MfR7R1A5S4S1cVsegs;RaS4dR8ScR8ZaA2M10S13R8A1SfR8A1A4S52R7S5bS15R7A1SeR7G10A2S2aSeR7ScR8ZbA2A2A1A3A2M11R1A5S1cVsegs;R9GfG11R1A5A2A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJd;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo Jd S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hsh & Hnn & Hnrw & Hceil & Hal & Hpos & Hfree & Hcont & Hnr & Hdisj & HJf & HJo & HJd).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_nw _ (ms_gpr ms 0) (ms_gpr ms 1) Hceil) as [En Hnw].
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@mmap_fixed_only_ok segs ms md); eassumption.
  - intros w' Hw.
    eapply (@wstep_mmap_fixed_inv segs ms md) in Hw; try eassumption. destruct Hw as [-> | [-> | ->]].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right; left. split.
      * rewrite <- G0, <- G1. rewrite after_sys_mem_with_mem.
        eapply smatch_after_ret_expr; [| | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
        -- apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
        -- split; [| apply mmap_fixed_ok_model_lazy; [exact Hnr | apply (model_idle_lazy Hh)]].
           unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Hnr), m_halted_vm_forget_range.
           apply (model_idle_halted Hh).
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
    + right; right. split.
      * rewrite <- G0, <- G1. unfold S_ret_lit, enomem_ret.
        eapply smatch_after_mem_lit.
        -- apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
        -- split; [| apply mmap_fixed_dead_model_lazy; apply (model_idle_lazy Hh)].
           unfold mmap_fixed_dead_model, with_mmap_destroyed. rewrite m_halted_vm_forget_range. apply (model_idle_halted Hh).
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJd.
Qed.

End Heap.
