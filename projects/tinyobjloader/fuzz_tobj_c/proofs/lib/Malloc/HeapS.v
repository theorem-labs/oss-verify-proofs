(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the forced mmap triples take the decline premise place_declined_b and the forced mmap inversions derive it from the step's answer, their refusal tests asked at the hint; the forced mprotect-expose inversion and triple, written as plain text, take the premise that the range misses the vDSO pair; the frame obligation's new cases closed by RomBase's tactics; RomBase imported). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "ms_svc_pending"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "false"; "Some"; "list"; "option"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "model_idle"; "triple1"; "wstep"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "mmap_fixed_ok_model"; "mmap_none_vm"; "mmap_place_ok"; "mmap_place_ok_none"; "mmap_rw_vm"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "event"; "map_contains"; "page_size"; "vm_maps"; "with_vmmaps"; "ENOMEM"; "errno_ret"; "alloc_top"; "region_free"; "two_pow_64"; "vm_noaccess"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "reg_sv"; "sobj"; "eval"; "ss_next"; "ss_objs"; "SLit"; "obj_range"; "ranges_disjoint"; "rm"; "ss_pc"; "sstate"; "sv"; "valuation"; "ro_addr"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "mmap_noaccess_b"; "mmap_fixed_noaccess_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "unmap_range"; "zero_range"; "after_sys"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframeJ"; "smatch_pending"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "S_ret_fresh"; "rho_after_unmap"; "rho_after_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "place_declined_b"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_kernel"; "page_round_up_Z"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable RomBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundR
  SymFrame SymCall SymHeap Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WstepForced.
  Variable segs : list Segment.

  Ltac msimp H :=
    cbv beta zeta delta [read_file_model openat_file_model openat_dir_model close_model
               mmap_rw_model mmap_none_model mmap_fixed_ok_model mmap_fixed_dead_model
               munmap_model with_mmap_destroyed with_mmap_replacement exit_model mprotect_model_next] in H;
    autorewrite with sys_input in H;
    try (rewrite with_mmap_backing_plain in H by assumption);
    autorewrite with model in H.
  Ltac mat_id Hm Hl :=
    erewrite materialize_model_accesses_no_lazy in Hm
      by (cbv beta zeta delta [read_file_model openat_file_model openat_dir_model close_model
                     mmap_rw_model mmap_none_model mmap_fixed_ok_model mmap_fixed_dead_model
                     munmap_model with_mmap_destroyed with_mmap_replacement mprotect_model_next];
          autorewrite with model; exact Hl);
    inversion Hm; subst.

  (* LPS 727298f3: decoded with this file's [tbs__] table and re-encoded, the refusal test asked
     at the hint.  Fw/SysSpec.v's [mmap_rw_inv_forced] takes the decline fact [place_declined_b
     ... = false] ([Hdecl]); it is not a premise here: the step's [Ok] answer implies it, and
     [mmap_rw_ok_not_declined] derives it from that answer (c3 clause 2). *)
  Lemma wstep_mmap_inv_forced : ltac2:(tb__ "0|0|
SeS23A1S1S22S12Q40A1S13S4SfS12Q40A1A1S3R4A1SdS12Q40A1R2A2A3S14R4A1S4S17S10Q40R4A2ZdeA3S6S4S12Q40A1S0R7U1A2S11Q40Z0A2A3A1S4S9S46S0R8U2A2S0R8U3A2S0R8U5A2A3SaA3S4S9S47S0R9U3A2A1ScA3S16Vsegs;SbSeS23A1S1fRbS20RaR9A2A4R7A3S7S5S4S9S4aS0RbU3A2S0RbU0A2RaS19S0RbU1A2A1A4SaA3S4S13R8SbSeS23A1S1fRcS20S4fRbS29S28A1A2RaA2A4A3A2S8S12Q40A1S12Q40A1S5S1cS0RcU0A2S0RcU3A2RbS0RcU1A2R1A5S4S13R9SbSeS23A1S1fRdS20S4cRcR1S4eS2RcA1R1S18S0RcU1A2A1A3A3S27S1eS21RbA1S0RcU1A2R1A3RbA2A2A4A3A2La;A2A2F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Hlen Hsh Hnr Hw.
    destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    pose proof (@mmap_rw_ok_not_declined (sys_input segs ms x8) m eff m' evs0 Hno Hlen Hsh
                  (syscall_spec_ns_spec _ _ _ Hspec)) as Hdecl.
    apply (@mmap_rw_inv_forced (sys_input segs ms x8) m Hno Hlen Hsh Hdecl) in Hspec.
    destruct Hspec as [[Hrf E] | (a & Hpl & E)]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact Hrf|]. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. exists a. split; [exact Hpl|].
      unfold mmap_rw_model in Hcases. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hcases.
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr) in Hcases.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  (* LPS 727298f3: decoded with this file's [tbs__] table and re-encoded, the refusal test asked
     at the hint.  Fw/SysSpec.v's [mmap_none_inv_forced] takes the decline fact
     [place_declined_b ... = false] ([Hdecl]); it is not a premise here: the step's [Ok] answer
     implies it, and [mmap_none_ok_not_declined] derives it from that answer (c3 clause 2). *)
  Lemma wstep_mmap_none_inv_forced : ltac2:(tb__ "0|0|
SeS23A1S1S22S12Q40A1S13S4SfS12Q40A1A1S3R4A1SdS12Q40A1R2A2A3S14R4A1S4S17S10Q40R4A2ZdeA3S6S4S12Q40A1S0R7U1A2S11Q40Z0A2A3A1S4S9S48S0R8U2A2S0R8U3A2S0R8U5A2A3SaA3S4S9S46S0R9U2A2S0R9U3A2S0R9U5A2A3ScA3S4S9S47S0RaU3A2A1ScA3S16Vsegs;SbSeS23A1S1fRcS20RbRaA2A4R8A3S7S5S4S9S4bS0RcU0A2RbS19S0RcU1A2A1A3SaA3S4S13R9SbSeS23A1S1fRdS20S4fRcS29S28A1A2RbA2A4A3A2S8S12Q40A1S12Q40A1S5S1dS0RdU0A2RcS0RdU1A2R1A4S4S13RaSbSeS23A1S1fReS20S4cRdR1S4dS2RdA1R1S18S0RdU1A2A1A3A3S27S1bS21RcA1S0RdU1A2R1A3RcA2A2A4A3A2La;A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Hlen Hsh Hnrw Hnr Hw.
    destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    pose proof (@mmap_none_ok_not_declined (sys_input segs ms x8) m eff m' evs0 Hno Hlen Hsh Hnrw
                  (syscall_spec_ns_spec _ _ _ Hspec)) as Hdecl.
    apply (@mmap_none_inv_forced (sys_input segs ms x8) m Hno Hlen Hsh Hnrw Hdecl) in Hspec.
    destruct Hspec as [[Hrf E] | (a & Hpl & E)]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact Hrf|]. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. exists a. split; [exact Hpl|].
      unfold mmap_none_model in Hcases. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hcases.
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr) in Hcases.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  (* RESTATED.  The old statement fails (measured) at
     HeapS.v:79 characters 92-95:
       The term "Hna" has type
        "map_contains (vm_noaccess (m_vmmaps m)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true"
       while it is expected to have type
        "region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
           (in_arg (sys_input segs ms x8) 0)
           (mmap_n (in_arg (sys_input segs ms x8) 1)) = true".
     [Hna] landed in [Hvd]'s SLOT: Section MprotectW (Fw/SysSpec.v:2501-2543) declares
     SIX hypotheses -- Hno, Hprot, Halign, Hlen, Hwrap, Hvd -- and Section Expose adds
     Hna and Hmp, so the discharged argument order of [mprotect_expose_inv_forced] is
     Hno Hprot Halign Hlen Hwrap Hvd Hna Hmp.  The call below passed eight arguments
     with [Hvd] missing.  [Hvd] is at :2543, whose own comment records why it exists:
     [check_mprotect] first answers unmodeled over the vDSO/vvar pair, so an mprotect
     that touches it is outside the modelled arm.  Counted off the Section's own
     declaration at a named sha, not off an environment dump.
     SIXTH member of the family this unit has been working through: triple1_munmapJ
     and etriple_munmapJ needed [maps_subtract ... = map_remove ...];
     triple1_mprotect_exposeJ and triple1_mprotect_noopJ
     needed exactly this [Hvd]; this is the [wstep] inversion twin of the first of
     those two, and [triple1_mprotect_exposeJ_forced] below is its consumer.
     The encoded statement was decoded from this file's own [tbs__] table and written
     out explicitly; the ONLY difference from the decoded text is the added premise,
     placed immediately after the [two_pow_64] one -- the position [Hvd] holds in
     Section MprotectW -- so the existing intro pattern reads in order.  NOTHING WAS
     RE-ENCODED; no record gains or loses a field.  The added premise is a HYPOTHESIS
     and the disjunctive conclusion is untouched, so no consumer's guarantee weakens. *)
  Lemma wstep_mprotect_expose_inv_forced :
    forall (ms : machine_state) (m : Model) (x8 : word) (tr : list event) (w' : world),
      bv_unsigned x8 = 226 ->
      bv_unsigned (ms_gpr ms 2) = 3 ->
      bv_unsigned (ms_gpr ms 0) mod page_size = 0 ->
      ms_gpr ms 1 <> Z_to_bv 64 0 ->
      bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64 ->
      region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
        (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true ->
      ms_svc_pending ms = Some x8 ->
      model_idle m ->
      map_contains (vm_noaccess (m_vmmaps m)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true ->
      map_contains (vm_maps (m_vmmaps m)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true ->
      wstep segs (tr, mkCfg ms m) w' ->
      mprotect_budget_ok m (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = false
      /\ w' = (tr, mkCfg (after_sys ms (errno_ret ENOMEM)) m)
      \/ mprotect_budget_ok m (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
         /\ w' = (tr, mkCfg (after_sys_mem ms (Z_to_bv 64 0)
                               (zero_range (ms_mem ms) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))
                            (mprotect_model_next m (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))).
  Proof using .
    intros ms m x8 tr w' Hno Hprot Halign Hlen Hwrap Hvd Hp Hi Hna Hmp Hw. pose proof Hi as [Hh Hl].
    destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@mprotect_expose_inv_forced (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hvd Hna Hmp) in Hspec.
    destruct Hspec as [[Hb E] | (Hb & E)]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact Hb|]. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. split; [exact Hb|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm (model_idle_lazy (mprotect_model_next_idle ms Hi)). now rewrite app_nil_r.
  Qed.

  Lemma wstep_mmap_fixed_inv_ok : ltac2:(tb__ "0|b|
S1S22S12Q40M0A1M1SeS23A1M2S13S4S17S10G0R3A2ZdeA3S6S4G1S0R6U1M3A2S11G0Z0M4A2A3A1S4S9S49S0R7U2M5A2S0R7U3M6A2S0R7U5M7A2A3SaA3S4S9S48S0R8G5A2S0R8G6A2S0R8G7A2A3ScA3S4S9S46S0R9G5A2S0R9G6A2S0R9G7A2A3ScA3S42S40S10G0S0RaU0M8A2A2S19S0RaG3A2A1A2S2aS21R9A1A1A2S4S17S43S10G0S0RbG8A2A2S25A2G4A3S41G4S10G0S0RcG8A2A2A2S4S9S2bS2eS21RcA1A1S0RdG8A2S18S0RdG3A2A1A3SaA3S4S9S24S26S21RdA1A1S0ReG8A2S18S0ReG3A2A1A3SaA3S4SfG1A1S3RfA1SdG1RdA2A3S14RfA1S4S9S47S0R11G6A2A1ScA3S16Vsegs;SbG2S1fRfS20R12R11A2A4ReA3S4S13RfSbG2S1fR10S20S4cR13S0R13G8A2M9S4dS2R13A1G9S18S0R13G3A2A1MaA3A3S1aS0R13G6A2R12G9GaA4A2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Ftr;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 tr w' Hno Hlen Hsh Hnn Hnrw Hceil Halign Hpos Hfree Hcont Hp [Hh Hl] Hnr Hw.
    destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@mmap_fixed_inv_ok (sys_input segs ms x8) m Hno Hlen Hsh Hnn Hnrw Hceil Halign Hpos Hfree Hcont) in Hspec.
    inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
    - mat_id Hm (mmap_fixed_ok_model_lazy ms m Hnr Hl). now rewrite app_nil_r.
    - exfalso. msimp Hcd. congruence.
  Qed.
End WstepForced.

Section HeapS.
Variable segs : list Segment.

(* LPS 727298f3: the J-premise's FIRST conjunct is now the decline premise [place_declined_b
   ... = false] of [mmap_*only_ok] ([wstep_mmap_*_inv_forced] derive it from the step's answer);
   the statement was decoded with this file's [tbs__] table (three names added at its end), the
   conjunct added and re-encoded, nothing else changed. *)
Theorem triple1_mmap_rwJ_forced : ltac2:(tb__ "0|0|
S13OF_;S30S30S12Q40A1S30F_;S3cS3eS31Vsegs;R6R5A3S51Vsegs;R7R6A3S4SfS44A1S59Vsegs;S3bR4A1A2SdS44S45A2A3S4S3dS32R5Z11A2S37ZdeA1A3SeS23A1S1S22S52Vsegs;R8R9SbSeS23A1S1fR3S20R2R1A2A4A4RdR9R4R2A3S5S4S9S5dS5eR3A1S21R3A1S0R4U0A2S5fS10Q40S0R4U1A2A2A1A4ScA3S5S6S4S12Q40A1S0R4U1A2S11Q40Z0A2A3A1S5S4S9S46S0R4U2A2S0R4U3A2S0R4U5A2A3SaA3S5S4S9S47S0R4U3A2A1ScA3S5S4S9S4aS0R4U3A2S0R4U0A2R3S19S0R4U1A2A1A4SaA3ReRbR6R4A3F_;S12Q40A1S1cS0R5U0A2S0R5U3A2R4S0R5U1A2R1A5S5S33S5aS33R1S36ReA1A3S39S38ReR2A2SbS17S17S10Q40R4A2S40S10Q40R4A2S19S0R8U1A2A1A2A4A2F_;Fo;S5S12Q40A1S5S42S10Q40R3A2S10Q40R1A2A2S41S10Q40R1A2S40S10Q40R3A2S19S0R7U1A2A1A2A2A2S4S9S3fVsegs;R2A2ScA3F_;Fx;ReR2S58RcS35RdA1R2R2S18S0R6U1A2A1A5R7S27S1eS21R5A1S0R6U1A2R2A3R5A2A4A2A2F_;Fa;A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S15Vsegs;RbS2fVsegs;RaR7R6A4S13S7S2fVsegs;RaS54R8S55A2R7R1A5S8S12Q40A1S12Q40A1S2fVsegs;RaR1A1S56R9A1S58R8S35R9A1R1R1S18S34R8S32R9ZbA2A2A1A5R2A5La;A2A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hmod & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mmap_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_inv_forced segs _ _ _ _ _ Hp Hh H222 Hlen Hmod Hnr Hw) as [[Hrf ->] | (a & Hpl & ->)].
    + left. split; [|exact (HJf Hrf)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
      split.
      * unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
        eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
        apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

(* LPS 727298f3: the J-premise's FIRST conjunct is now the decline premise [place_declined_b
   ... = false] of [mmap_*only_ok] ([wstep_mmap_*_inv_forced] derive it from the step's answer);
   the statement was decoded with this file's [tbs__] table (three names added at its end), the
   conjunct added and re-encoded, nothing else changed. *)
Theorem triple1_mmap_noneJ_forced : ltac2:(tb__ "0|0|
S13OF_;S30S30S12Q40A1S30F_;S3cS3eS31Vsegs;R6R5A3S51Vsegs;R7R6A3S4SfS44A1S59Vsegs;S3bR4A1A2SdS44S45A2A3S4S3dS32R5Z11A2S37ZdeA1A3SeS23A1S1S22S52Vsegs;R8R9SbSeS23A1S1fR3S20R2R1A2A4A4RdR9R4R2A3S5S4S9S5dS5eR3A1S21R3A1S0R4U0A2S5fS10Q40S0R4U1A2A2A1A4ScA3S5S6S4S12Q40A1S0R4U1A2S11Q40Z0A2A3A1S5S4S9S48S0R4U2A2S0R4U3A2S0R4U5A2A3SaA3S5S4S9S46S0R4U2A2S0R4U3A2S0R4U5A2A3ScA3S5S4S9S47S0R4U3A2A1ScA3S5S4S9S4bS0R4U0A2R3S19S0R4U1A2A1A3SaA3ReRbR6R4A3F_;S12Q40A1S1dS0R5U0A2R4S0R5U1A2R1A4S5S33S5aS33R1S36ReA1A3S39S38ReR2A2SbS17S17S10Q40R4A2S40S10Q40R4A2S19S0R8U1A2A1A2A4A2F_;Fo;ReR2S57RcS35RdA1R2R2S18S0R6U1A2A1A5R7S27S1bS21R5A1S0R6U1A2R2A3R5A2A4A2F_;Fa;A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S15Vsegs;RbS2fVsegs;RaR7R6A4S13S7S2fVsegs;RaS54R8S55A2R7R1A5S8S12Q40A1S12Q40A1S2fVsegs;RaR1A1S56R9A1S57R8S35R9A1R1R1S18S34R8S32R9ZbA2A2A1A5R2A5La;A2A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hna & Hmod & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mmap_none_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_none_inv_forced segs _ _ _ _ _ Hp Hh H222 Hlen Hna Hmod Hnr Hw) as [[Hrf ->] | (a & Hpl & ->)].
    + left. split; [|exact (HJf Hrf)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
      split.
      * unfold S_ret_fresh, rho_after_unmap. rewrite <- G1.
        eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
        apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

(* RESTATED, same cause and same conjunct as
   [wstep_mprotect_expose_inv_forced] above: this theorem is that lemma's only consumer in
   this unit (through `try eassumption` below), so once the lemma asks for [Hvd] this
   J-premise must carry it.  The statement was decoded from this file's own [tbs__] table and
   written out explicitly; the ONLY difference from the decoded text is the added conjunct,
   placed immediately after the [two_pow_64] one, which is both [Hvd]'s position in Section
   MprotectW and the position the sibling [triple1_mprotect_exposeJ] (Fw3/SymHeap.v, which
   compiles, measured) puts it.  Nothing re-encoded; the
   added conjunct is a HYPOTHESIS and the disjunctive postcondition is untouched.
   CONSUMERS, both read at the tip: P/Mal_ameta__G4.v:652 and U/Mal_ameta__G4.v:652, which
   [refine] this theorem and prove the J-premise in tactic text, so each gains one visible
   goal rather than a silent weakening. *)
Theorem triple1_mprotect_exposeJ_forced :
  forall (ok : world -> Prop) (J Jf Jo : jpred) (S : sstate) (rho : valuation),
    ok_frameJ segs ok J ->
    ok_pframeJ segs ok J ->
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 226 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        bv_unsigned (ms_gpr ms 2) = 3
        /\ bv_unsigned (ms_gpr ms 0) mod page_size = 0
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64
        /\ region_free (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md)))
             (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
        /\ map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = true
        /\ map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = true
        /\ (mprotect_budget_ok md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = false ->
              Jf rho tr md)
        /\ (mprotect_budget_ok md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned (ms_gpr ms 0),
                    bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1)))
              /\ (forall x, bv_unsigned (ms_gpr ms 0) <= bv_unsigned x
                              < bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) ->
                    ro_addr segs x = false)
              /\ Jo (set_rm rho (zero_range (rm rho) (ms_gpr ms 0)
                                   (mmap_n (ms_gpr ms 1)))) tr
                   (mprotect_model_next md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))) ->
    triple1 segs ok (SPJ segs J S rho)
      (fun w => SPJ segs Jf (S_ret_lit S enomem_ret) rho w
                \/ SPJ segs Jo (S_ret_lit S 0)
                     (set_rm rho (zero_range (rm rho) (eval rho (reg_sv S 10))
                                    (mmap_n (eval rho (reg_sv S 11))))) w).
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hvd & Hna & Hmp & HJf & HOK).
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold two_pow_64 in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mprotect_expose_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (wstep_mprotect_expose_inv_forced segs ms md) in Hw; try eassumption. destruct Hw as [[Hb ->] | (Hb & ->)].
    + left. split; [|exact (HJf Hb)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. destruct (HOK Hb) as (Hdisj & Hnro & HJo). split.
      * unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
        eapply smatch_after_mem_lit; [| apply mprotect_model_next_idle; exact Hh].
        apply smatch_pending_rezero; [exact Hsp | unfold two_pow_64 in Hwrap; lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
Qed.

Theorem triple1_mmap_fixedJ_ok : ltac2:(tb__ "0|f|
S13OF_;S30S30S3cS3eS31Vsegs;R5R4A3S51Vsegs;R6R5A3S4SfS44A1S59Vsegs;S3bR4A1A2SdS44S45A2A3S4S3dS32R5Z11A2S37ZdeA1A3SeS23A1M0S1S22S52Vsegs;R8R9SbG0S1fR3S20R2R1A2A4A4RcR9R4R2A3S5S6S4S12Q40M1A1S0R4U1M2A2M3S11G1Z0M4A2A3A1S5S4S9S49S0R4U2A2M5S0R4U3A2M6S0R4U5A2M7A3SaA3S5S4S9S48G5G6G7A3ScA3S5S4S9S46G5G6G7A3ScA3S5S42S40S10G1S0R4U0M8A2M9A2MaS19G3A1A2S2aS21R3A1MbA1A2S5S4S17S43GaS25A2G4A3S5S41G4GaA2S5S4S9S2bS2eGbA1G9S18G3A1McA3SaA3S5S4S9S24S26GbA1G9GcA3SaA3S5S4S9S47G6A1ScA3S5S33S5aS33R1S36RcA1A3S39S38RcR2A2SbS17S17S10G1S0R6G8A2A2MdS40GdS19S0R6G2A2A1A2A4A2F_;Fo;RcS50RaS4dS3aRaA1G9GcA3A2R5S1aG6R3G9GcA4A3A2A2A2A2A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S15Vsegs;RaS2fVsegs;R9R7R6A4S13S2fVsegs;R9S53R8S32R8ZaA2MeS36R8A1S35R8A1A4S50R7S4dS3aR7A1S34R7GeA2S18S34R7S32R8ZbA2A2A1A3A2R1A5Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJo;FJ;Fok;").
Proof using .
  intros ok J Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hsh & Hnn & Hnrw & Hceil & Hal & Hpos & Hfree & Hcont & Hnr & Hdisj & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_nw _ (ms_gpr ms 0) (ms_gpr ms 1) Hceil) as [En Hnw].
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mmap_fixed_only_ok segs ms md); eassumption.
  - intros w' Hw.
    eapply (wstep_mmap_fixed_inv_ok segs ms md) in Hw; try eassumption. subst w'.
    split.
    + rewrite <- G0, <- G1. rewrite after_sys_mem_with_mem.
      eapply smatch_after_ret_expr; [| | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
      * apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
      * split; [| apply mmap_fixed_ok_model_lazy; [exact Hnr | apply (model_idle_lazy Hh)]].
        unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Hnr), m_halted_vm_forget_range.
        apply (model_idle_halted Hh).
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
Qed.
End HeapS.
