(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (not_refusable_of_place written as plain text over the hint, with a nonzero length and an address at or above task_unmapped_base, Linux's bottom-up window; wstep_mmap_inv_grantedA written as plain text, its refusability test at the hint, the decline fact place_declined_b derived from the step's answer; the two granted mmap triples take a NULL hint, from which the decline test is computed; the frame obligation's new cases closed by RomBase's tactics). *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "ms_svc_pending"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "eval"; "ss_next"; "reg_sv"; "ss_objs"; "SLit"; "SVar"; "obj_range"; "ranges_disjoint"; "ro_addr"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@Corelib.Init.Datatypes"; "bool"; "false"; "pair"; "list"; "true"; "Some"; "option"; "app"; "cons"; "fst"; "nil"; "prod"; "snd"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "ge"; "modulo"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "wstep"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "m_halted"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "mmap_n"; "mmap_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA"; "mmap_obj_sym"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "zero_range"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable RomBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundM SymSoundR SymSoundL SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
Import ListNotations.
Open Scope Z_scope.

Section G.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

(* Written out as plain text (decoded from this file's [tbs__] table).  [mmap_grant_refusable]
   (Fw/Refusable.v) takes four arguments, flags, hint, md, nZ; the hint is [addr], the one
   [mmap_place_ok addr flags m len a] names.
   LPS 727298f3 (with 08b1429): [mmap_grant_refusable] asks Linux's placement at the hint
   ([vm_place_available]), not a free gap anywhere below [alloc_top].  A free gap gives Linux an
   address only inside Linux's bottom-up window, so the gap's address must be at or above the
   model's [task_unmapped_base] and the request must be a nonzero length
   ([vm_place_available_of_gap]); the two premises say so. *)
Lemma not_refusable_of_place :
  forall (addr flags : word) (m : Model) (len a : word),
    0 < bv_unsigned len ->
    task_unmapped_base <= bv_unsigned a ->
    mmap_place_ok addr flags m len a ->
    mmap_grant_refusable flags addr m (mmap_nZ len) = false.
Proof.
  intros addr flags m len a Hlen Hlo (Hal & Hpos & Htop & Hfree & Hb).
  assert (Hnpos : 0 < mmap_nZ len).
  { unfold mmap_nZ, page_round_up_Z, page_size.
    pose proof (Z.div_mod (bv_unsigned len + 4096 - 1) 4096 ltac:(lia)) as H.
    pose proof (Z.mod_pos_bound (bv_unsigned len + 4096 - 1) 4096 ltac:(lia)) as Hr. lia. }
  assert (Hnal : mmap_nZ len mod page_size = 0).
  { unfold mmap_nZ, page_round_up_Z, page_size. apply Z_mod_mult. }
  unfold mmap_grant_refusable. rewrite Hb. cbn [negb orb].
  rewrite (vm_place_available_of_gap _ _ _ _ a Hnpos Hnal Hal Hlo Htop ltac:(exact Hfree)).
  reflexivity.
Qed.

(* Written out as plain text (decoded from this file's [tbs__] table); its refusability test
   takes the hint, as above.  LPS 727298f3: Fw/SysSpec.v's [mmap_rw_inv_granted] takes the
   decline fact [place_declined_b ... = false]; it is not a premise here: the step's [Ok] answer
   implies it, and [mmap_rw_ok_not_declined] derives it from that answer (c3 clause 2). *)
Lemma wstep_mmap_inv_grantedA : forall ms m x8,
  m_halted m = None ->
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) m (mmap_nZ (ms_gpr ms 1)) = false ->
  forall tr (w' : world),
  ms_svc_pending ms = Some x8 ->
  wstep (tr, mkCfg ms m) w' ->
  exists a, mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) m (ms_gpr ms 1) a
    /\ w' = (tr, mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a (mmap_n (ms_gpr ms 1))))
                       (mmap_rw_model (ms_gpr ms 3) m (ms_gpr ms 1) a)).
Proof.
  intros ms m x8 Hh Hno Hlen Hsh Hnr tr w' Hp Hw.
  destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
  pose proof (@mmap_rw_ok_not_declined (sys_input segs ms x8) m eff m' evs0 Hno Hlen Hsh
                (syscall_spec_ns_spec _ _ _ Hspec)) as Hdecl.
  apply (@mmap_rw_inv_granted (sys_input segs ms x8) m Hno Hlen Hsh Hdecl _ Hnr) in Hspec.
  destruct Hspec as (a & Hpl & E). inversion E; subst.
  exists a. split; [exact Hpl|].
  destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
  - cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
    injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
  - exfalso. revert Hcd. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
    change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1). rewrite mmap_rw_model_halted. congruence.
Qed.

(* LPS 727298f3: a premise [reg_sv (ax_S A) 10 = SLit 0] (the hint a0 is NULL) is inserted right
   after the [reg_sv (ax_S A) 17 = SLit 222] premise, and nothing else changed (decoded with this
   file's [tbs__] table, the premise added, re-encoded).  The decline test is computed from it.
   The same for [etriple_mmap_rw_symA_granted] below. *)
Theorem triple1_mmap_rw_symA_granted : ltac2:(tb__ "0|0|
S34OF_;S4cS9Q40A1S4cF_;S1dS18S22S9Q40A1A1SbS2dS4eVsegs;R8R7A3S52Vsegs;R9R8A3S4dVsegs;SeS19R7A1A1R9A3S0S25S42A1S50Vsegs;S16S19R8A1A1A2S24S42S43A2A3S0SbSfS19R9A1Z11A2S11ZdeA1A3S0SbSfS19RaA1ZaA2S11Z0A1A3S0SbSfS19RbA1ZbA2R8A3S0S1fS17SeS19RcA1A1R9A2S23A3S0S2dS8Q40SdRcRaA2A2R9A3S0S2dS32RaZ1000A2Z0A3S1S2eZ0RbA2S2eRbS33Z2Z3eA2A2A2S22S3bA1S5S3aS51Vsegs;R12R11R13S21S22S3bA1S38R3S39R2R1A2A4A5R16R13R12R4R2A4S1S0S1fS40S4R4U2A2S4R4U3A2S4R4U5A2A3S23A3S1S0S1fS41S4R4U3A2A1S20A3S1S31S53R3R13A2R11A2S1S0S1fS3fS4R4U3A2S4R4U0A2R3S44S4R4U1A2A1A4S20A3S9Q40A1S45S4R5U0A2S4R5U3A2R4S4R5U1A2R1A5S1ScS4fScR1S10S19R18A1A1A3S14S13R18R2A2S21S2dS2dS8Q40R4A2S2fS8Q40R4A2R15A2A4A2F_;Fo;S1S9Q40A1S1S30S8Q40R3A2S8Q40R1A2A2S2eS8Q40R1A2S2fS8Q40R3A2R14A2A2A2S0S1fS15Vsegs;R2A2S20A3F_;Fx;S1S2aSbSbA2S2dS4fS2aSbSbA2R2S1aR19A1A3S1S30S8Q40SdR19S28SbSbR3A3A2A2R2A2S2eR2S2fS8Q40SdR19S28SbSbR3A3A2A2S8Q40SdR19S2bSbSbR3A3A2A2A2A2A2S3S1S30S8Q40R6A2S8Q40S1eS8Q40SdR1aS1bR1bA1A2A2R3A2A2A2S2eS8Q40S1eS8Q40SdR1aS1bR1bA1A2A2R3A2A2S2fS8Q40R6A2R17A2A2A2A1F_;F_;Fy;Fr;R18R2S49R16SeS19R17A1A1R2A3R15R7S3dS46S3cR5A1S4R6U1A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S36Vsegs;R14S4bVsegs;R13R11R10RfA5S34S2S9Q40A1S9Q40A1S4bVsegs;R14R1A1S1cR13S4aS19R13A1S12SeS19R13A1A1A1S26ScS10S19R13A1A1S27ScS54SeS19R13A1A1R10A2S29ScA1A3A3S55SeS19R13A1A1A1A4A2S49R12SeS19R13A1A1R1A3R11R2A6La;A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJ;Fok;").
Proof using .
  intros ok J Jo A rho tp elen nlit Hokf Hokp Hst Hi H17 H10 H11 Hbel Helen Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & Hnref & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hdecl : place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
                    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false).
  { destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite G0, H10.
    exact (place_declined_b_null _ _ _). }
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). apply (mmap_only_okA segs ms md _ Hh H222 Hlen Hmodb Hdecl).
  - intros w' Hw. destruct (wstep_mmap_inv_grantedA ms md _ Hh H222 Hlen Hmodb Hnref tr w' Hp Hw) as (a & Hpl & ->).
    exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
    + eapply smatchA_after_mmap_obj_sym; eauto.
    + cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.

Theorem etriple_mmap_rw_symA_granted : ltac2:(tb__ "0|0|
S4cS9Q40A1S4cF_;S1dS18S22S9Q40A1A1SbS2dS4dVsegs;SeS19R5A1A1R7A3S0S25S42A1S50Vsegs;S16S19R6A1A1A2S24S42S43A2A3S0SbSfS19R7A1Z11A2S11ZdeA1A3S0SbSfS19R8A1ZaA2S11Z0A1A3S0SbSfS19R9A1ZbA2R6A3S0S1fS17SeS19RaA1A1R7A2S23A3S0S2dS8Q40SdRaR8A2A2R7A3S0S2dS32R8Z1000A2Z0A3S1S2eZ0R9A2S2eR9S33Z2Z3eA2A2A2S22S3bA1S5S3aS51Vsegs;R10RfR11S21S22S3bA1S38R3S39R2R1A2A4A5R14R11R10R4R2A4S1S0S1fS40S4R4U2A2S4R4U3A2S4R4U5A2A3S23A3S1S0S1fS41S4R4U3A2A1S20A3S1S31S53R3R11A2RfA2S1S0S1fS3fS4R4U3A2S4R4U0A2R3S44S4R4U1A2A1A4S20A3S9Q40A1S45S4R5U0A2S4R5U3A2R4S4R5U1A2R1A5S1ScS4fScR1S10S19R16A1A1A3S14S13R16R2A2S21S2dS2dS8Q40R4A2S2fS8Q40R4A2R13A2A4A2F_;Fo;S1S9Q40A1S1S30S8Q40R3A2S8Q40R1A2A2S2eS8Q40R1A2S2fS8Q40R3A2R12A2A2A2S0S1fS15Vsegs;R2A2S20A3F_;Fx;S1S2aSbSbA2S2dS4fS2aSbSbA2R2S1aR17A1A3S1S30S8Q40SdR17S28SbSbR3A3A2A2R2A2S2eR2S2fS8Q40SdR17S28SbSbR3A3A2A2S8Q40SdR17S2bSbSbR3A3A2A2A2A2A2S3S1S30S8Q40R6A2S8Q40S1eS8Q40SdR18S1bR19A1A2A2R3A2A2A2S2eS8Q40S1eS8Q40SdR18S1bR19A1A2A2R3A2A2S2fS8Q40R6A2R15A2A2A2A1F_;F_;Fy;Fr;R16R2S49R14SeS19R15A1A1R2A3R13R7S3dS46S3cR5A1S4R6U1A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S35Vsegs;S4bVsegs;R11RfReRdA5S34S2S9Q40A1S9Q40A1S4bVsegs;R12R1A1S1cR11S4aS19R11A1S12SeS19R11A1A1A1S26ScS10S19R11A1A1S27ScS54SeS19R11A1A1ReA2S29ScA1A3A3S55SeS19R11A1A1A1A4A2S49R10SeS19R11A1A1R1A3RfR2A6La;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp elen nlit Hst Hi H17 H10 H11 Hbel Helen Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & Hrf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hdecl : place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
                    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false).
  { destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite G0, H10.
    exact (place_declined_b_null _ _ _). }
  destruct (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hlen Hrf) as (a & Hpl & Hlp).
  change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
  eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb Hdecl tr a Hp Hpl Hlp)|].
  exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
  - eapply smatchA_after_mmap_obj_sym; eauto.
  - cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.
End G.
