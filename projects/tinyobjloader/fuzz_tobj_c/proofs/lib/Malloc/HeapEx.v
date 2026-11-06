(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "false"; "Some"; "list"; "option"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_sub"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "reg_sv"; "sobj"; "SLit"; "ss_pc"; "sstate"; "sv"; "valuation"; "eval"; "rm"; "ss_next"; "ss_objs"; "obj_range"; "ranges_disjoint"; "ro_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_n"; "mmap_none_vm"; "mmap_place_ok_none"; "mmap_fixed_ok_model"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "modulo"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "map_contains"; "page_size"; "vm_maps"; "two_pow_64"; "vm_noaccess"; "with_vmmaps"; "region_free"; "vm_brk"; "vm_start_brk"; "alloc_top"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "S_after"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "rho_after_unmap"; "S_ret_fresh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "zero_range"; "unmap_range"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noaccess_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "brk_grow_ok"; "brk_model_next"; "mmap_fixed_noaccess_b"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"].
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
  SymFrame SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HeapExRules.
Variable segs : list Segment.

Theorem etriple_mmap_none_okJ : ltac2:(tb__ "0|9|
S14SfQ40M0A1M1S14F_;S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19ZdeA1A3ScS31A1M2S6S30S40Vsegs;R6R7S9G2S2eR3S2fR2R1A2A4A4RaR7R4R2A3S0S2S1G1S5R4U1M3A2S10G0Z0A2A3A1S0S1S7S4dS5R4U2A2M4S5R4U3A2M5S5R4U5A2M6A3S8A3S0S1S7S4cG4G5G6A3SaA3S0S1S7S4eG5A1SaA3S3G1G1S0S28S5R5U0A2R4S5R5G3A2M7R1A4S0S18S4bS18R1S21RbA1A3S23S22RbR2A2S9S12S12SeG0R3A2M8S2aG8S25S5R7G3A2A1A2A4A2F_;Fo;RbR1S47R9S20RaA1R1R1S26G7A1A5R6S38S27S32R4A1G7R1A3R4A2A4A2A2La;A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R7R5R4A4S3fS3G1G1S13Vsegs;R8R1A1S48R7A1S47R6S20R7A1R1R1S26S1eR6S17R7ZbA2A2A1A5R2A5La;A2Lw;A3F_;F_;F_;Frho;FS;FJo;FJ;").
Proof using .
  intros J Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hna & Hmod & Hnr & a & Hpl & Hdisj & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
  eexists. split; [eapply (@wstep_mmap_none_intro_ok segs tr ms); eassumption|].
  exists a. split.
  - unfold S_ret_fresh, rho_after_unmap. rewrite <- G1.
    eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
    apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

Theorem etriple_mmap_none_failJ : ltac2:(tb__ "0|6|
S14S14S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19ZdeA1A3ScS31A1M0S6S30S40Vsegs;R6R7S9G0S2eR3S2fR2R1A2A4A4RaR7R4R2A3S0S2S1SfQ40M1A1S5R4U1A2M2S10G1Z0A2A3A1S0S1S7S4dS5R4U2A2M3S5R4U3A2M4S5R4U5A2M5A3S8A3S0S1S7S4cG3G4G5A3SaA3S0S1S7S4fR3S25G2A1A2S8A3RaR8R5R3A3A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R7R5R4A4S13Vsegs;R6S45R5S46A2R4A4A3F_;F_;F_;Frho;FS;FJf;FJ;").
Proof using .
  intros J Jf S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hna & Hmod & Hrf & HJf).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  eexists. split; [eapply (@wstep_mmap_none_intro_fail segs tr ms); eassumption|].
  split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem etriple_brk_grow_failJ : forall (J Jf : jpred) (S : sstate) (rho : valuation) (b0 : word),
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 214 ->
  (forall (tr : list event) (ms : machine_state) (md : Model),
     smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     vm_brk (m_vmmaps md) = b0 /\
     bv_unsigned (vm_start_brk (m_vmmaps md)) <= bv_unsigned b0 /\
     bv_unsigned b0 < bv_unsigned (ms_gpr ms 0) /\
     LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok md (ms_gpr ms 0) (ms_gpr ms 0) = false /\
     Jf (rho_set_rw rho (ss_next S) b0) tr md) ->
  etriple segs (SPJ segs J S rho) (SPJ segs Jf (S_ret_fresh S) (rho_set_rw rho (ss_next S) b0)).
Proof using .
  intros J Jf S rho b0 Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hb0 & Hsb & Hlt & Hg & HJf). subst b0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  eexists. split; [eapply (@wstep_brk_grow_intro_fail segs tr ms); eassumption|].
  split.
  - unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJf.
Qed.

Theorem etriple_brk_grow_okJ : ltac2:(tb__ "0|b|
S14S14S1bS1dSfQ40M0A1M1S1SdS15A1S43Vsegs;S1aR3A1A2SbS15S16A2A3S1S1cS17R4Z11A2S19Zd6A1A3ScS31A1M2S6S30S40Vsegs;R7R8S9G2S2eR3S2fR2R1A2A4A4RbR8R4R2A3S0S1G1S3aS32R3A1M3A1R8A3S0S2dSeG0S3bG3A1A2SeG0R8A2M4A2S0S1S12S2cG4S34A2Z0M5A3S0S1S12S2cSeG0S5R4U0M6A2M7A2M8S34A2G5A3S0S0S2bG5G4A2S2bG4G8A2A2S0S1S7S50R3G7G7A3S8A3S0S18S4bS18R1S21RbA1A3S23S22RbR2A2S9S12S12SeG0RaA2SeG0S5R6G6A2A2A4A2F_;Fo;S0G1S0S2dSeG0R9A2SeG0R1A2M9A2S2bG9SeG0S5R5G6A2A2A2A2S1S7S24Vsegs;R2A2SaA3F_;Fx;RbS44R9S49S1fR9A1R8S11G0G7R8A3A3A2R5S38S51G3G7G7A3R3A2A3A2A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R8R6R5A4S13Vsegs;R7S41R6S17R6ZaA2MaS21R6A1S20R6A1A4S44R5S49S1fR5A1R4S11G0S1eR5GaA2R4A3A3A2A4A3F_;F_;F_;Fb0;Frho;FS;FJo;FJ;").
Proof using .
  intros J Jo S rho b0 Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hb0 & Hsb & Halo & Halr & Hlt & Hg & Hdisj & Hnro & HJo). subst b0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  eexists. split; [eapply (@wstep_brk_grow_intro_ok segs tr ms); try eassumption; lia|].
  rewrite (brk_eff_grow_aligned (m_vmmaps md) (ms_gpr ms 0) Halo Halr Hlt).
  change (eff_mem ms (mkEffect (ms_gpr ms 0) [] [(vm_brk (m_vmmaps md), (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv)]))
    with (zero_range (ms_mem ms) (vm_brk (m_vmmaps md)) (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv).
  pose proof (urange (ms_gpr ms 0)) as Hr0.
  assert (En : bv_unsigned (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv = bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps md))).
  { rewrite bv_sub_unsigned. apply bv_wrap_small. rewrite two64. lia. }
  split.
  - rewrite <- G0. rewrite after_sys_mem_with_mem.
    eapply smatch_after_ret_expr; [| split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)] | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
    apply smatch_pending_rezero; [exact Hsp | rewrite En; lia | rewrite En | rewrite En].
    + intros o Ho. replace (bv_unsigned (vm_brk (m_vmmaps md)) + (bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps md)))) with (bv_unsigned (ms_gpr ms 0)) by lia. exact (Hdisj o Ho).
    + intros x Hx. apply Hnro. lia.
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0. exact HJo.
Qed.

Theorem etriple_mprotect_expose_failJ : ltac2:(tb__ "0|8|
S14S14S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19Ze2A1A3ScS31A1M0S6S30S40Vsegs;R6R7S9G0S2eR3S2fR2R1A2A4A4RaR7R4R2A3S0S1S12SeQ40M1S5R4U2A2A2Z3A3S0S1S12S2cSeG1S5R4U0A2M2A2M3S34A2Z0M4A3S0S2S1SfG1A1S5R4U1A2M5S10G1G4A2A3A1S0S2bS2aG3S25G5A1A2S36A2S0S1S7S33S37S32R3A1M6A1G2S26G5A1M7A3S8A3S0S1S7S33S35G6A1G2G7A3S8A3S0S1S7S53R3G2G7A3SaA3RaR8R5R3A3A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R7R5R4A4S13Vsegs;R6S45R5S46A2R4A4A3F_;F_;F_;Frho;FS;FJf;FJ;").
Proof using .
  intros J Jf S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hna & Hmp & Hb & HJf).
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  eexists. split; [eapply (@wstep_mprotect_expose_intro_fail segs ms md); eassumption|].
  split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem etriple_mprotect_expose_okJ : ltac2:(tb__ "0|e|
S14S14S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19Ze2A1A3ScS31A1M0S6S30S40Vsegs;R6R7S9G0S2eR3S2fR2R1A2A4A4RaR7R4R2A3S0S1S12SeQ40M1S5R4U2A2A2Z3A3S0S1S12S2cSeG1S5R4U0M2A2M3A2M4S34A2Z0M5A3S0S2S1SfG1A1M6S5R4U1M7A2M8S10G1G5A2A3A1S0S2bS2aG4S25G8A1A2S36A2S0S1S7S33S37S32R3A1M9A1G3S26G8A1MaA3S8A3S0S1S7S33S35G9A1G3GaA3S8A3S0S1S7S53R3G3GaA3S8A3S0S18S4bS18R1S21RaA1A3S23S22RaR2A2S9S12S12SeG1S5R6G2A2A2MbS2aGbS25S5R6G7A2A1A2A4A2F_;Fo;S0G6S0S2dSeG1S5R5G2A2A2McSeG1R1A2MdA2S2bGdS2aGcS25S5R5G7A2A1A2A2A2S1S7S24Vsegs;R2A2SaA3F_;Fx;RaS44R8S49S1fR8A1G3GaA3A2R5S54R3G3GaA3A3A2A2A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R7R5R4A4S13Vsegs;R6S45R5G5A2S44R4S49S1fR4A1S1eR4S17R5ZaA2A2S26S1eR4S17R5ZbA2A2A1A3A2A4A3F_;F_;F_;Frho;FS;FJo;FJ;").
Proof using .
  intros J Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hna & Hmp & Hb & Hdisj & Hnro & HJo).
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold two_pow_64 in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  eexists. split; [eapply (@wstep_mprotect_expose_intro_ok segs ms md); eassumption|].
  split.
  - unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
    eapply smatch_after_mem_lit; [| apply mprotect_model_next_idle; exact Hh].
    apply smatch_pending_rezero; [exact Hsp | unfold two_pow_64 in Hwrap; lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
Qed.

Theorem etriple_mprotect_noopJ : ltac2:(tb__ "0|9|
S14S14S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19Ze2A1A3ScS31A1M0S6S30S40Vsegs;R6R7S9G0S2eR3S2fR2R1A2A4A4RaR7R4R2A3S0S1S12SeQ40M1S5R4U2A2A2Z3A3S0S1S12S2cSeG1S5R4U0A2M2A2M3S34A2Z0M4A3S0S2S1SfG1A1S5R4U1A2M5S10G1G4A2A3A1S0S2bS2aG3S25G5A1A2S36A2S0S1S7S33S37S32R3A1M6A1M7G2S26G5A1M8A3SaA3S0S1S7S33S35G6A1G2G8A3S8A3S0S1S7S39G7G2G8A3S8A3RaR8R5R3A3A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R7R5R4A4S13Vsegs;R6S45R5G4A2R4A4A3F_;F_;F_;Frho;FS;FJ';FJ;").
Proof using .
  intros J J' S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hna & Hmp & Hrf & HJ').
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  eexists. split; [eapply (@wstep_mprotect_noop_intro segs ms md); eassumption|].
  split; [|exact HJ']. unfold S_ret_lit. change 0 with (bv_unsigned (Z_to_bv 64 0)).
  eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem etriple_mmap_fixed_okJ : ltac2:(tb__ "0|f|
S14S14S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19ZdeA1A3ScS31A1M0S6S30S40Vsegs;R6R7S9G0S2eR3S2fR2R1A2A4A4RaR7R4R2A3S0S2S1SfQ40M1A1S5R4U1M2A2M3S10G1Z0M4A2A3A1S0S1S7S52S5R4U2A2M5S5R4U3A2M6S5R4U5A2M7A3S8A3S0S1S7S4dG5G6G7A3SaA3S0S1S7S4cG5G6G7A3SaA3S0S2dS2aSeG1S5R4U0M8A2M9A2MaS25G3A1A2S3cS32R3A1MbA1A2S0S1S12S2cGaS34A2G4A3S0S2bG4GaA2S0S1S7S39S3dGbA1G9S26G3A1McA3S8A3S0S1S7S33S35GbA1G9GcA3S8A3S0S1S7S4eG6A1SaA3S0S18S4bS18R1S21RaA1A3S23S22RaR2A2S9S12S12SeG1S5R6G8A2A2MdS2aGdS25S5R6G2A2A1A2A4A2F_;Fo;RaS44R8S4aS1fR8A1G9GcA3A2R5S29G6R3G9GcA4A3A2A2A2A2A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R7R5R4A4S13Vsegs;R6S41R5S17R5ZaA2MeS21R5A1S20R5A1A4S44R4S4aS1fR4A1S1eR4GeA2S26S1eR4S17R5ZbA2A2A1A3A2A4A3F_;F_;F_;Frho;FS;FJo;FJ;").
Proof using .
  intros J Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hsh & Hnn & Hnrw & Hceil & Hal & Hpos & Hfree & Hcont & Hnr & Hdisj & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_nw _ (ms_gpr ms 0) (ms_gpr ms 1) Hceil) as [En Hnw].
  eexists. split; [eapply (@wstep_mmap_fixed_intro_ok segs ms md); eassumption|].
  split.
  - rewrite <- G0, <- G1. rewrite after_sys_mem_with_mem.
    eapply smatch_after_ret_expr; [| | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
    + apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
    + split; [| apply mmap_fixed_ok_model_lazy; [exact Hnr | apply (model_idle_lazy Hh)]].
      unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Hnr), m_halted_vm_forget_range.
      apply (model_idle_halted Hh).
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
Qed.

Theorem etriple_mmap_none_anyJ : ltac2:(tb__ "0|a|
S14S14SfQ40M0A1M1S14F_;S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19ZdeA1A3ScS31A1M2S6S30S40Vsegs;R6R7S9G2S2eR3S2fR2R1A2A4A4RbR7R4R2A3S0S2S1G1S5R4U1M3A2M4S10G0Z0A2A3A1S0S1S7S4dS5R4U2A2M5S5R4U3A2M6S5R4U5A2M7A3S8A3S0S1S7S4cG5G6G7A3SaA3S0S1S7S4eG6A1SaA3S0S1S7S4fR3S25G4A1A2S8A3RcR9R6R4A3F_;G1S28S5R5U0A2R4S5R5G3A2R1A4S0S18S4bS18R1S21RcA1A3S23S22RcR2A2S9S12S12SeG0R4A2M8S2aG8S25S5R8G3A2A1A2A4A2F_;Fo;RcR2S47RaS20RbA1R2R2S26S5R6G3A2M9A1A5R7S38S27S32R5A1G9R2A3R5A2A4A2F_;Fa;A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R8R5R4A4S3fS4S13Vsegs;R8S45R6S46A2R5R1A5S3G1G1S13Vsegs;R8R1A1S48R7A1S47R6S20R7A1R1R1S26S1eR6S17R7ZbA2A2A1A5R2A5La;A2A2Lw;A3F_;F_;F_;Frho;FS;FJo;FJf;FJ;").
Proof using .
  intros J Jf Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hna & Hmod & Hnr & HJf & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_reserve_refusable md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [eapply (@wstep_mmap_none_intro_fail segs tr ms); eassumption|].
    left. split; [|exact (HJf eq_refl)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
  - assert (Hpl' : exists a, mmap_place_ok_none (ms_gpr ms 0) md (ms_gpr ms 1) a).
    { exact (@mmap_none_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf). }
    destruct Hpl' as [a Hpl]. destruct (HJo a Hpl) as (Hdisj & HJoa).
    pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
    eexists. split; [eapply (@wstep_mmap_none_intro_ok segs tr ms); eassumption|].
    right. exists a. split.
    + unfold S_ret_fresh, rho_after_unmap. rewrite <- G1.
      eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
      apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJoa.
Qed.

Theorem etriple_mprotect_expose_anyJ : ltac2:(tb__ "0|11|
S14S14S14S1bS1dS1SdS15A1S43Vsegs;S1aR2A1A2SbS15S16A2A3S1S1cS17R3Z11A2S19Ze2A1A3ScS31A1M0S6S30S40Vsegs;R6R7S9G0S2eR3S2fR2R1A2A4A4RbR7R4R2A3S0S1S12SeQ40M1S5R4U2A2A2Z3A3S0S1S12S2cSeG1S5R4U0M2A2M3A2M4S34A2Z0M5A3S0S2S1SfG1A1M6S5R4U1M7A2M8S10G1G5A2A3A1S0S2bS2aG4S25G8A1A2S36A2S0S1S7S33S37S32R3A1M9A1G3S26G8A1MaA3S8A3S0S1S7S33S35G9A1G3GaA3S8A3S0S1S7S53R3G3GaA3MbSaA3RcR9R6R4A3F_;S1S7GbS8A3S0S18S4bS18R1S21RbA1A3S23S22RbR2A2S9S12S12SeG1S5R7G2A2A2McS2aGcS25S5R7G7A2A1A2A4A2F_;Fo;S0G6S0S2dSeG1S5R6G2A2A2MdSeG1R1A2MeA2S2bGeS2aGdS25S5R6G7A2A1A2A2A2S1S7S24Vsegs;R2A2SaA3F_;Fx;RbS44R9S49S1fR9A1S5R5G2A2MfS26S5R5G7A2A1M10A3A2R6S54R4GfG10A3A3A2A2F_;A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S3eVsegs;S13Vsegs;R8R5R4A4S3fS4S13Vsegs;R8S45R6S46A2R5R1A5S13Vsegs;R7S45R6G5A2S44R5S49S1fR5A1S1eR5S17R6ZaA2A2S26S1eR5S17R6ZbA2A2A1A3A2R1A5A2Lw;A3F_;F_;F_;Frho;FS;FJo;FJf;FJ;").
Proof using .
  intros J Jf Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hna & Hmp & HJf & HJo).
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  destruct (mprotect_budget_ok md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))) eqn:Hb.
  - destruct (HJo eq_refl) as (Hdisj & Hnro & HJoo).
    assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
    { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
      unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
      unfold two_pow_64 in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
    eexists. split; [eapply (@wstep_mprotect_expose_intro_ok segs ms md); eassumption|].
    right. split.
    + unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
      eapply smatch_after_mem_lit; [| apply mprotect_model_next_idle; exact Hh].
      apply smatch_pending_rezero; [exact Hsp | unfold two_pow_64 in Hwrap; lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJoo.
  - eexists. split; [eapply (@wstep_mprotect_expose_intro_fail segs ms md); eassumption|].
    left. split; [|exact (HJf eq_refl)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

End HeapExRules.

