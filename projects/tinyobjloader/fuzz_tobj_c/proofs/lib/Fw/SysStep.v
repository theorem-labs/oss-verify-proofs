(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "iff"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_svc_pending"; "ms_read_byte"; "ms_mem"; "ms_regs"; "ms_pc"; "ms_writable_byte"; "write_to_mem"; "ms_fcsr"; "ms_fregs"; "ms_resv"; "ms_rom"; "Build_machine_state"; "set_reg"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkCfg"; "config"; "sys_input"; "advance_past_svc"; "apply_effect"; "sstep"; "step_to"; "SError"; "SNext"; "apply_unmaps"; "apply_zeros"; "unmodeled_at"; "apply_writes"; "zeros_cover"; "@Corelib.Init.Datatypes"; "pair"; "option"; "list"; "Some"; "bool"; "nil"; "prod"; "cons"; "None"; "true"; "false"; "app"; "nat"; "length"; "andb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "SyscallEffect"; "m_halted"; "m_fds"; "errno_ret"; "fd_lookup"; "read_cstr"; "m_fs"; "MemCopy"; "m_vmmaps"; "cstr_result"; "mkEffectU"; "CstrOk"; "map_contains"; "vm_maps"; "vm_brk"; "alloc_fd"; "FdChannel"; "TASK_SIZE"; "ENOMEM"; "ExitEv"; "m_vm_lazy"; "read_bytes_map"; "vm_noaccess"; "in_arg"; "m_killed"; "m_tid"; "map_has"; "with_vmmaps"; "FdFile"; "region_free"; "vm_start_brk"; "with_fds"; "ENOENT"; "ENOTTY"; "FdDir"; "KillEv"; "MAX_RW_COUNT"; "WriteEv"; "materialize_model_accesses"; "page_size"; "syscall_effect_accesses"; "with_tid"; "EBADF"; "EISDIR"; "fd_insert"; "EFAULT"; "ENAMETOOLONG"; "SyscallInput"; "access_okb"; "alloc_top"; "eff_copies"; "eff_ret"; "eff_unmaps"; "eff_writes"; "eff_zeros"; "fd_remove"; "in_mem"; "in_sysno"; "in_wmem"; "two_pow_64"; "vm_reserved"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "model_idle"; "world"; "wstep"; "tcons"; "ok_src"; "ok_tgt"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "after_sys_mem"; "unmap_range"; "zero_range"; "in_range"; "eff_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "cmd32"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.WithImage"; "only_ok"; "det_succ"; "exited"; "openat_path_errno"; "closed_model"; "exit_code"; "@Stdlib.ZArith.BinInt.Z"; "le"; "ldiff"; "lt"; "add"; "modulo"; "of_nat"; "leb"; "ltb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open"; "open_ignored_flags"; "path_is_dirref"; "openat_errnos"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "Unmodeled"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "AT_FDCWD32"; "TIOCGWINSZ"; "dot_path"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "path"; "file_read"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "mmap_modeled_b"; "mmap_noaccess_b"; "munmap_free_ok"; "brk_grow_ok"; "brk_model_next"; "mmap_fixed_noaccess_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "is_ret_ci"; "is_ret"; "mmap_n";
"openat_dir_model"; "mmap_fixed_ok_model"; "munmap_model"; "brk_eff"; "mmap_fixed_dead_model"; "mmap_none_vm"; "mmap_place_ok"; "mmap_place_ok_none"; "mmap_rw_vm"; "openat_file_model"; "openat_reads"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei"; "path_has_slash"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess"; "rw_bytes_max"; "delivered_writes"; "@LinuxProcessSemantics.Riscv.Sem"; "reg_get"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "@LinuxProcessSemantics.Riscv.Prelude"; "bvmap"; "bvmap_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "sstep_a"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Set Implicit Arguments.

Section Input.
  Variable segs : list Segment.

  Lemma sys_input_sysno : ltac2:(tb__ "0|1|
S7S15Q40A1M0S0G0S72S1bVsegs;R2R1A3A1R1A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_arg0 : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0G0S50S1bVsegs;R2R1A3U0M1A2S6R2G1A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_arg1 : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0G0S50S1bVsegs;R2R1A3U1M1A2S6R2G1A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_arg2 : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0G0S50S1bVsegs;R2R1A3U2M1A2S6R2G1A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_arg3 : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0G0S50S1bVsegs;R2R1A3U3M1A2S6R2G1A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_arg4 : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0G0S50S1bVsegs;R2R1A3U4M1A2S6R2G1A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_arg5 : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0G0S50S1bVsegs;R2R1A3U5M1A2S6R2G1A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_mem : ltac2:(tb__ "0|1|
S7S15Q40A1M0S0G0S28S15Q8A1A1F_;S71S1bVsegs;R2R1A3A1S9R2A1A3Fx8;Fms;").
  Proof using . reflexivity. Qed.
  Lemma sys_input_wmem : ltac2:(tb__ "0|1|
S7S15Q40A1M0S0G0S28S15Q8A1A1F_;S73S1bVsegs;R2R1A3A1SdVsegs;R2A2A3Fx8;Fms;").
  Proof using . reflexivity. Qed.

  Lemma ms_gpr_reg : ltac2:(tb__ "0|0|
S7S33S0S15Q40A1S6R2R1A2SbfSbR2A1S17Q5S90ZaS92R1A1A2A2A2A3Fk;Fms;").
  Proof using . reflexivity. Qed.
End Input.

Create HintDb sys_input.
#[export] Hint Rewrite sys_input_sysno sys_input_arg0 sys_input_arg1 sys_input_arg2
  sys_input_arg3 sys_input_arg4 sys_input_arg5 sys_input_mem sys_input_wmem : sys_input.

Definition after_sys_mem (ms : machine_state) (r : word) (mem : word -> option byte)
    : machine_state := ltac2:(tb__ "0|3|
S13Sc7Q5M0S15Q40M1A1M2S17G0ZaA2Vr;SbVms;A1A5S10Vms;A1S18G1ScVms;A1S17G1Z4A2A3S2fG2A1S11Vms;A1SfVms;A1Vmem;S12Vms;A1A8").

Definition after_sys (ms : machine_state) (r : word) : machine_state := ltac2:(tb__ "0|0|
S7fVms;Vr;SaVms;A1A3").

Definition eff_mem (ms : machine_state) (eff : SyscallEffect) : word -> option byte := ltac2:(tb__ "0|0|
S25S23S22SaVms;A1S6dVeff;A1A2S6fVeff;A1A2S6eVeff;A1A2").

Lemma advance_apply_effect : ltac2:(tb__ "0|0|
S7S39S0S29S40A1S6bR1A1S2cS40A1A3S0S7S1cS1dR3R2A2A1S7fR3S6cR2A1S83R3R2A2A3A3F_;Feff;Fms;").
Proof. intros ms [r ws zs us cs ci] H. cbn in H. subst cs. reflexivity. Qed.

Lemma advance_apply_ret_ci : ltac2:(tb__ "0|2|
S7S15Q40A1M0S29S2dG0S33A2A1S0S7S1cS1dR3S43R2S2cS2dG0S29S15Q8A1A1A2A1S2cS2dG0G0A2A1M1G1S2cS40A1R1A6A2A1S7eR3R2A2A3Fci;Fr;Fms;").
Proof. reflexivity. Qed.

Lemma advance_apply_ret : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0S7S1cS1dR2S43R1S2cS2dG0S29S15Q8A1A1A2A1S2cS2dG0G0A2A1M1G1S2cS40A1S2cS2dG0S33A2A1A6A2A1S7eR2R1A2A3Fr;Fms;").
Proof. reflexivity. Qed.

Lemma apply_effect_ret : ltac2:(tb__ "0|2|
S7S15Q40A1M0S0S7S1dR2S43R1S2cS2dG0S29S15Q8A1A1A2A1S2cS2dG0G0A2A1M1G1S2cS40A1S2cS2dG0S33A2A1A6A2S14R2S17Q5ZaA2R1A3A3Fr;Fms;").
Proof. reflexivity. Qed.

Lemma advance_apply_write1 : ltac2:(tb__ "0|4|
S7S15Q40A1M0G0S29S15Q8A1A1M1S0S7S1cS1dR4S43R3S2eS2dG0G1A2M2S27G0G1R2R1A4S2cG2A1A3S2cS2dG0G0A2A1M3G3S2cS40A1S2cS2dG0S33A2A1A6A2A1S7fR4R3SeSaR4A1R2R1A3A3A3Fbs;Fa;Fr;Fms;").
Proof. reflexivity. Qed.

Lemma advance_apply_delivered : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0S29S15Q8A1A1S0S7S1cS1dR4S43R3SbeR2R1A2S2cS2dG0G0A2A1M1G1S2cS40A1S2cS2dG0S33A2A1A6A2A1S7fR4R3SeSaR4A1R2R1A3A3A3Fbs;Fa;Fr;Fms;").
Proof. intros ms r a [|b bs]; reflexivity. Qed.

Definition in_range (a n x : word) : bool := ltac2:(tb__ "0|3|
S35S93S16Q40M0Va;A2M1S16G0Vx;A2M2A2S94G2S90G1S16G0Vn;A2A2A2A2").

Definition zero_range (mem : word -> option byte) (a n : word) : word -> option byte := ltac2:(tb__ "0|2|
S23Vmem;S2eS2dS15Q40A1M0G0A2M1S27G0G0Va;Vn;A4S2cG1A1A3A2").

Definition unmap_range (mem : word -> option byte) (a n : word) : word -> option byte := ltac2:(tb__ "0|2|
S22Vmem;S2eS2dS15Q40A1M0G0A2M1S27G0G0Va;Vn;A4S2cG1A1A3A2").

Lemma zeros_cover_1 : ltac2:(tb__ "0|2|
S15Q40A1M0G0G0S0S2bS26S2eS2dG0G0A2M1S27G0G0R3R2A4S2cG1A1A3R1A2S82R3R2R1A3A3Fx;Fn;Fa;").
Proof. intros. unfold zeros_cover, in_range. cbn. now rewrite orb_false_r. Qed.

Lemma zero_range_at : ltac2:(tb__ "0|4|
S15Q40A1M0S28S15Q8M1A1M2A1M3F_;G0G0G0S0G3S81R4R3R2R1A4S2bG3L_;S82R3R2R1A3S2aG2S17G1Z0A2A2R4R1A1X2bx2A3Fx;Fn;Fa;Fmem;").
Proof. intros. unfold zero_range. cbn [apply_zeros]. now rewrite zeros_cover_1. Qed.

Lemma unmap_range_at : ltac2:(tb__ "0|3|
S15Q40A1M0S28S15Q8A1M1A1M2F_;G0G0G0S0G2S80R4R3R2R1A4S2bG2L_;S82R3R2R1A3S2fG1A1R4R1A1X2bx2A3Fx;Fn;Fa;Fmem;").
Proof. intros. unfold unmap_range. cbn [apply_unmaps]. now rewrite zeros_cover_1. Qed.

Lemma in_range_spec : ltac2:(tb__ "0|4|
S15Q40M0A1M1G1G1S5S0S2bS82R3R2R1A3S30A3S1S8dS16G0R3A2M2S16G0R1A2M3A2S8fG3S90G2S16G0R2A2A2A2A2A2Fx;Fn;Fa;").
Proof.
  intros. unfold in_range. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma advance_apply_zero1 : ltac2:(tb__ "0|3|
S7S15Q40A1M0G0G0S0S7S1cS1dR4S43R3S2cS2dG0S29S15Q8A1A1A2A1S2eS2dG0G0A2M1S27G0G0R2R1A4S2cG1A1M2A3G2S2cS40A1S2cS2dG0S33A2A1A6A2A1S7fR4R3S81SaR4A1R2R1A3A3A3Fn;Fa;Fr;Fms;").
Proof. reflexivity. Qed.

Lemma advance_apply_unmap1 : ltac2:(tb__ "0|3|
S7S15Q40A1M0G0G0S0S7S1cS1dR4S43R3S2cS2dG0S29S15Q8A1A1A2A1S2cS2dG0G0A2M1A1M2S2eG1S27G0G0R2R1A4G2A3S2cS40A1S2cS2dG0S33A2A1A6A2A1S7fR4R3S80SaR4A1R2R1A3A3A3Fn;Fa;Fr;Fms;").
Proof. reflexivity. Qed.

Lemma after_sys_pc : ltac2:(tb__ "0|2|
S7S15Q40M0A1M1G1S28S15Q8A1A1F_;S0G1ScS7fR3R2R1A3A1S18G0ScR3A1S17G0Z4A2A3A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.
Lemma after_sys_pending : ltac2:(tb__ "0|1|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S0S28G0A1S8S7fR3R2R1A3A1S2fG0A1A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.
Lemma after_sys_memq : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0S28S15Q8A1A1F_;M1S0G1SaS7fR3R2R1A3A1R1A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.
Lemma after_sys_rom : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0S28S15Q8A1A1F_;M1S0G1S12S7fR3R2R1A3A1S12R3A1A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.
Lemma after_sys_fregs : ltac2:(tb__ "0|1|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S0Sc6Q5G0A2S10S7fR3R2R1A3A1S10R3A1A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.
Lemma after_sys_fcsr : ltac2:(tb__ "0|1|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S0S15Q20A1SfS7fR3R2R1A3A1SfR3A1A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.
Lemma after_sys_resv : ltac2:(tb__ "0|1|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S0S28G0A1S11S7fR3R2R1A3A1S11R3A1A3Fmem;Fr;Fms;").
Proof. reflexivity. Qed.

Lemma after_sys_a0 : ltac2:(tb__ "0|1|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S0G0SbfSbS7fR3R2R1A3A1S17Q5ZaA2A2R2A3Fmem;Fr;Fms;").
Proof.
  intros. unfold reg_get. cbn [ms_regs after_sys_mem]. now rewrite bvmap_get_set_same.
Qed.

Lemma after_sys_reg_other : ltac2:(tb__ "0|3|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S15Q5M1A1M2S2S0G2R1S17G1ZaA2A3A1S0G0SbfSbS7fR5R4R3A3A1R2A2SbfSbR5A1R2A2A3F_;Fk;Fmem;Fr;Fms;").
Proof.
  intros ms r mem k Hk. unfold reg_get. cbn [ms_regs after_sys_mem].
  rewrite bvmap_get_set_other; [reflexivity|]. congruence.
Qed.

Lemma after_sys_gpr0 : ltac2:(tb__ "0|1|
S7S15Q40A1M0G0S28S15Q8A1A1F_;S0G0S6S7fR3R2R1A3U0A2R2A3Fmem;Fr;Fms;").
Proof. intros. unfold ms_gpr. apply after_sys_a0. Qed.

Lemma advance_past_svc_fields : ltac2:(tb__ "0|3|
S7S1S0Sc6Q5S15Q40M0A1M1A2SbS1cR1A1M2A1SbR1A1A3S1S0G1S28S15Q8A1A1F_;SaG2A1SaR1A1A3S1S0G1ScG2A1S18G0ScR1A1S17G0Z4A2A3A3S0S28G1A1S8G2A1S2fG1A1A3A2A2A2Fms;").
Proof. intros ms. repeat split; reflexivity. Qed.

Section WithImage.
  Variable segs : list Segment.

  Notation wstep := (wstep segs).

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

  Lemma sstep_pending_inv : ltac2:(tb__ "0|b|
S7S37S15Q40A1M0S29S36A1M1S1fS0S28G0A1M2S8R5A1S2aG0R3A2A3S0G2S3aR5A1S2fG0A1M3A3S1eVsegs;S19R7R6A2R4R3A4S3S4S39S39S4S37S37S4G1G1S1S86S1bVsegs;RbR9A3RaS98S39R3R2R1A4A3S3S1S0G2S3aR2A1G3A3M4S1S0G1R8R1A3S4S37S37S1S0S28S37A1M5S5fR3S61R4A1A2S2aS37R1A2A3S0S1fR8S21S19S1cS1dRcR4A2A1R1A2A1A3A2Lm'';A2A2A2S3S1G4S1S0G1R8S2cS36A1M6A3S1S0G5S5fR2S61R3A1A2S2fS37A1A3S0S1fR7S20A3A2A2A2S3S4G0G0S1S0G2S3aR3A1S2aG0R1A2M7A3S1S0G2S51R3A1M8G3A3S1S0G1R9S32S36R2S2eS36S4cR1S3fR3A1M9A2G6A3A3A3S0S1fR8S21S19RcR3A2A1A3MaA2A2A2Lcode;A2S4G0G0S1S0G2G8G7A3S1S0G1R9S32S36R2S2eS36S5cR1G9A2G6A3A3A3GaA2A2Lsig;A2A2A2A2A2Levs0;A2Lm';A2Leff;A2S1S86S1bVsegs;R8R6A3R7S9aS39A1A3S1S0S1fR4S20A3S0G1R5G6A3A2A2A2F_;F_;F_;Fto;Fevs;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 evs to Hp Hh Hs.
    inversion Hs; subst; try congruence.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [eassumption|]. left. eauto.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [eassumption|]. right; left. eauto.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [eassumption|]. right; right; left. eexists. eauto.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [eassumption|]. right; right; right. eexists. eauto.
    -
      right. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      auto.
  Qed.


  Lemma m_killed_some_halted : ltac2:(tb__ "0|2|
S37S15Q40A1M0S0S28G0A1M1S51R2A1S2aG0R1A2A3S0G1S3aR3A1S2aG0R2A2A3F_;Fsig;Fm;").
  Proof using .
    intros m sig H. unfold m_killed, m_halted in *.
    destruct (procst_killed (m_proc m)); [exact H | discriminate].
  Qed.

  Lemma sstep_a_pending_inv_ns : ltac2:(tb__ "0|b|
S7S37S15Q40A1M0S29S36A1M1S1fS0S28G0A1M2S8R5A1S2aG0R3A2A3S0G2S3aR5A1S2fG0A1M3A3Sc9Vsegs;S19R7R6A2R4R3A4S3S4S39S39S4S37S37S4G1G1S1Sc8S1bVsegs;RbR9A3RaS98S39R3R2R1A4A3S3S1S0G2S3aR2A1G3A3M4S1S0G1R8R1A3S4S37S37S1S0S28S37A1M5S5fR3S61R4A1A2S2aS37R1A2A3S0S1fR8S21S19S1cS1dRcR4A2A1R1A2A1A3A2Lm'';A2A2A2S3S1G4S1S0G1R8S2cS36A1M6A3S1S0G5S5fR2S61R3A1A2S2fS37A1A3S0S1fR7S20A3A2A2A2S3S4G0G0S1S0G2S3aR3A1S2aG0R1A2M7A3S1S0G2S51R3A1M8G3A3S1S0G1R9S32S36R2S2eS36S4cR1S3fR3A1M9A2G6A3A3A3S0S1fR8S21S19RcR3A2A1A3MaA2A2A2Lcode;A2S4G0G0S1S0G2G8G7A3S1S0G1R9S32S36R2S2eS36S5cR1G9A2G6A3A3A3GaA2A2Lsig;A2A2A2A2A2Levs0;A2Lm';A2Leff;A2S1S86S1bVsegs;R8R6A3R7S9aS39A1A3S1S0S1fR4S20A3S0G1R5G6A3A2A2A2F_;F_;F_;Fto;Fevs;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 evs to Hp Hh Hs. unfold sstep_a in Hs.
    inversion Hs; subst; try congruence.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [split; [eassumption|]|].
      + intros e1 m1 v1 E _. injection E as <- <- <-. assumption.
      + left. eauto.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [split; [eassumption|]|].
      + intros e1 m1 v1 E _. injection E as <- <- <-. assumption.
      + right; left. eauto.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [split; [eassumption|]|].
      + intros e1 m1 v1 E Hg. injection E as <- <- <-. congruence.
      + right; right; left. eexists. eauto.
    -
      left. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      eexists _, _, _. split; [split; [eassumption|]|].
      + intros e1 m1 v1 E Hg. injection E as <- <- <-.
        pose proof (@m_killed_some_halted _ _ ltac:(eassumption)).
        congruence.
      + right; right; right. eexists. eauto.
    -
      right. match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end.
      auto.
  Qed.


  Lemma sstep_pending_run : ltac2:(tb__ "0|2|
S7S37S15Q40A1M0S39S37S29S36A1S0S28G0A1M1S8R6A1S2aG0R4A2A3S0G1S3aR6A1S2fG0A1A3Sc8S1bVsegs;R8R6A3R7S98S39R5R4R3A4A3S77R5A1Sc9Vsegs;S19RaR9A2R5S21S19S1cS1dRaR7A2A1R6A2A1A4F_;F_;F_;F_;Fevs;Fm';Feff;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 eff m' evs Hp Hh [Hs Hns] [Hh' Hl']. unfold sstep_a.
    eapply sstep_cfg_syscall;
      [exact Hh | exact Hp | exact Hs | exact (Hns _ _ _ eq_refl ltac:(congruence)) | exact Hh'
      | apply materialize_model_accesses_no_lazy; exact Hl'].
  Qed.

  Lemma sstep_pending_exit : ltac2:(tb__ "0|3|
S7S37S15Q40A1M0S39S37S29S36A1G0S0S28G0A1M1S8R7A1S2aG0R5A2A3S0G1S3aR7A1S2fG0A1M2A3S86S1bVsegs;R9R7A3R8S98S39R6R5R4A4A3S0G1S3aR6A1S2aG0R4A2A3S0G1S51R7A1G2A3Sc9Vsegs;S19RcRbA2S32S36R7S2eS36S4cR6S3fR8A1A2S2cS36A1A3A3S21S19RcR8A2A1A4F_;F_;F_;F_;F_;Fcode;Fevs;Fm';Feff;Fx8;Fm;Fms;").
  Proof using . intros. unfold sstep_a. eapply sstep_cfg_exit; eauto. Qed.

  Definition only_ok (i : SyscallInput) (m : Model) : Prop := ltac2:(tb__ "0|2|
S1S2S86Vi;Vm;S9aS39A1A3A1S39S37S29S36A1S86Vi;Vm;S98S39R3R2R1A4A3S0S28S15Q40A1M0A1S3aR3A1S2fG0A1A3S0S29S2dG0G0A2M1A1S4dR4A1S2cG1A1A3F_;F_;Fevs;Fm';Feff;A2").

  Lemma only_ok_of_inv : ltac2:(tb__ "0|3|
S68S37S99S39A1M0OF_;G0S86R4R3R1A3R3R2A1F_;FR;S2R2S9aS39A1A1A1S39S37S29S36A1R6S98S39R3R2R1A4A1S0S28S15Q40A1M1A1S3aR3A1S2fG1A1A3S0S29S2dG1G1A2M2A1S4dR4A1S2cG2A1A3F_;F_;Fevs;Fm';Feff;S87R6R5A2F_;F_;F_;FP;Fm;Fi;").
  Proof using .
    intros i m P Hinv Hn Hl. split.
    - intros Hs. exact (Hn (Hinv _ Hs)).
    - intros eff m' evs Hs Hh. exact (Hl _ _ _ (Hinv _ Hs) Hh).
  Qed.

  Lemma pending_no_error : ltac2:(tb__ "0|1|
S7S37S15Q40A1M0S29S36A1S0S28G0A1S8R4A1S2aG0R2A2A3S87S1bVsegs;R5R3A3R4A2S2S1eVsegs;S19R6R5A2R3S20A4A1F_;F_;Fevs;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 evs Hp [Hok Hl] Hs. inversion Hs; subst; try congruence;
      match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end;
      try match goal with H : materialize_model_accesses ?m1 _ = None |- _ =>
        rewrite materialize_model_accesses_no_lazy in H; [discriminate|]; eapply Hl; eauto end;
      exact (Hok ltac:(assumption)).
  Qed.

  Lemma pending_not_unmodeled_at : ltac2:(tb__ "0|1|
S7S37S15Q40A1M0S0S28G0A1S8R3A1S2aG0R1A2A3S87S1bVsegs;R4R2A3R3A2S2S24Vsegs;S19R5R4A2A2A1F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 Hp [Hok _] [_ [[Hn _] | (x & Hx & Hs)]]; cbn in *; [congruence|].
    rewrite Hp in Hx. inversion Hx; subst. exact (Hok Hs).
  Qed.

  Lemma ok_src_pending : ltac2:(tb__ "0|2|
S29S36A1M0OF_;G0S7S37S15Q40A1M1S7aR5R4A2S0S28G1A1S8R4A1S2aG1R2A2A3S87S1bVsegs;R5R3A3R4A2S7bVsegs;R8S27G0S1aR7S19R6R5A2A4A3F_;F_;F_;Fx8;Fm;Fms;Ftr;FSpec;").
  Proof using .
    intros Spec tr ms m x8 Ht Hp Hok. split; [exact Ht|]. cbn.
    exact (pending_not_unmodeled_at Hp Hok).
  Qed.

  Lemma ok_tgt_pending : ltac2:(tb__ "0|2|
S29S36A1M0OF_;G0S7S37S15Q40A1M1S7aR5R4A2S0S28G1A1S8R4A1S2aG1R2A2A3S87S1bVsegs;R5R3A3R4A2S7cVsegs;R8S27G0S1aR7S19R6R5A2A4A3F_;F_;F_;Fx8;Fm;Fms;Ftr;FSpec;").
  Proof using .
    intros Spec tr ms m x8 Ht Hp Hok. split; [exact Ht|]. cbn. intros evs.
    exact (pending_no_error (evs:=evs) Hp Hok).
  Qed.

  Lemma halted_no_sstep : ltac2:(tb__ "0|1|
S7S37S15Q40A1M0S29S36A1S1fS0S28G0A1S3aR4A1S2aG0R3A2A3S2S1eVsegs;S19R6R5A2R3R2A4A1F_;Fto;Fevs;Fcode;Fm;Fms;").
  Proof using . intros ms m code evs to Hh Hs. inversion Hs; subst; congruence. Qed.

  Lemma halted_no_wstep : ltac2:(tb__ "0|2|
S29S36A1M0S7S37S15Q40A1M1S78S0S28G1A1S3aR3A1S2aG1R2A2A3S2S79Vsegs;S27G0S1aR6S19R5R4A2A4R2A3A1F_;Fw';Fcode;Fm;Fms;Ftr;").
  Proof using . intros tr ms m code w' Hh (evs & Hs & _). exact (halted_no_sstep Hh (sstep_cfg_sub _ _ _ _ _ Hs)). Qed.

  Lemma wstep_pending_inv : ltac2:(tb__ "0|9|
S29S36A1M0S7S37S15Q40A1M1S78S0S28G1A1M2S8R4A1S2aG1R2A2A3S0G2S3aR4A1S2fG1A1M3A3S79Vsegs;S27G0S1aR7S19R6R5A2A4R3A3S4S39S39S4S37S37S4G0G0S1S86S1bVsegs;RaR8A3R9S98S39R3R2R1A4A3S3S1S0G2S3aR2A1G3A3S4S37S37S1S0S28S37A1S5fR3S61R4A1A2S2aS37R1A2A3S0S78R8S27G0S1aS32S36RcR2A3S19S1cS1dRbR4A2A1R1A2A4A3A2Lm'';A2A2S4G1G1S1S0G2S3aR3A1S2aG1R1A2M4A3S3S1S0G2S51R3A1M5G3A3S0S78R8S27G0S1aS32S36RcS32S36R2S2eS36S4cR1S3fR3A1M6A2S2cS36A1M7A3A3A3S19RbR3A2M8A4A3A2S1S0G2G5G4A3S0S78R8S27G0S1aS32S36RcS32S36R2S2eS36S5cR1G6A2G7A3A3A3G8A4A3A2A2A2Lcode;A2A2A2Levs0;A2Lm';A2Leff;A2F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 [tr' c'] Hp Hh (evs & Hs & Htr). cbn in Hs, Htr. subst tr'.
    destruct (sstep_pending_inv Hp Hh (sstep_cfg_sub _ _ _ _ _ Hs))
      as [(eff & m' & evs0 & Hspec & [(Hh' & -> & m'' & Hm & E) | [(_ & _ & _ & E) | [(code & Hc & Hk & -> & E) | (sig & Hk & -> & E)]]]) | (_ & E & _)];
      [| discriminate | | | discriminate].
    - inversion E; subst. exists eff, m', evs0. split; [exact Hspec|]. left. eauto.
    - inversion E; subst. exists eff, m', evs0. split; [exact Hspec|]. right.
      exists code. split; [exact Hc|]. left. rewrite app_assoc. auto.
    - inversion E; subst. exists eff, m', evs0. split; [exact Hspec|]. right.
      exists sig. split; [exact (@m_killed_some_halted _ _ Hk)|]. right. rewrite app_assoc. auto.
  Qed.

  Lemma wstep_pending_inv_ns : ltac2:(tb__ "0|9|
S29S36A1M0S7S37S15Q40A1M1S78S0S28G1A1M2S8R4A1S2aG1R2A2A3S0G2S3aR4A1S2fG1A1M3A3S79Vsegs;S27G0S1aR7S19R6R5A2A4R3A3S4S39S39S4S37S37S4G0G0S1Sc8S1bVsegs;RaR8A3R9S98S39R3R2R1A4A3S3S1S0G2S3aR2A1G3A3S4S37S37S1S0S28S37A1S5fR3S61R4A1A2S2aS37R1A2A3S0S78R8S27G0S1aS32S36RcR2A3S19S1cS1dRbR4A2A1R1A2A4A3A2Lm'';A2A2S4G1G1S1S0G2S3aR3A1S2aG1R1A2M4A3S3S1S0G2S51R3A1M5G3A3S0S78R8S27G0S1aS32S36RcS32S36R2S2eS36S4cR1S3fR3A1M6A2S2cS36A1M7A3A3A3S19RbR3A2M8A4A3A2S1S0G2G5G4A3S0S78R8S27G0S1aS32S36RcS32S36R2S2eS36S5cR1G6A2G7A3A3A3G8A4A3A2A2A2Lcode;A2A2A2Levs0;A2Lm';A2Leff;A2F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 [tr' c'] Hp Hh (evs & Hs & Htr). cbn in Hs, Htr. subst tr'.
    destruct (sstep_a_pending_inv_ns Hp Hh Hs)
      as [(eff & m' & evs0 & Hspec & [(Hh' & -> & m'' & Hm & E) | [(_ & _ & _ & E) | [(code & Hc & Hk & -> & E) | (sig & Hk & -> & E)]]]) | (_ & E & _)];
      [| discriminate | | | discriminate].
    - inversion E; subst. exists eff, m', evs0. split; [exact Hspec|]. left. eauto.
    - inversion E; subst. exists eff, m', evs0. split; [exact Hspec|]. right.
      exists code. split; [exact Hc|]. left. rewrite app_assoc. auto.
    - inversion E; subst. exists eff, m', evs0. split; [exact Hspec|]. right.
      exists sig. split; [exact (@m_killed_some_halted _ _ Hk)|]. right. rewrite app_assoc. auto.
  Qed.


  Lemma wstep_pending_inv_idle : ltac2:(tb__ "0|c|
S29S36A1M0S7S37S15Q40A1M1S78S39S37G0S0S28G1A1M2S8R7A1S2aG1R5A2A3S0G2S3aR7A1S2fG1A1M3A3M4S79Vsegs;S27G0S1aRaS19R9R8A2A4R6A3S99S39A1M5S86S1bVsegs;RbR9A3RaR1A3S0G5R2S98S39R8R7R6A4A3F_;FR;S0S29S2dG1G1A2M6A1S4dR6A1S2cG6A1A3S3S1G4S0S78R9S27G0S1aS32S36RdR6A3S19S1cS1dRcR8A2A1R7A2A4A3A2S4G1G1S1S0G2S3aR8A1S2aG1R1A2M7A3S3S1S0G2S51R8A1M8G3A3S0S78RaS27G0S1aS32S36ReS32S36R7S2eS36S4cR1S3fR8A1M9A2S2cS36A1MaA3A3A3S19RdR8A2MbA4A3A2S1S0G2G8G7A3S0S78RaS27G0S1aS32S36ReS32S36R7S2eS36S5cR1G9A2GaA3A3A3GbA4A3A2A2A2Lcode;A2A2F_;F_;F_;F_;F_;Fevs0;Fm';Feff;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' eff m' evs0 Hp Hh Hw Hinv Hl.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff1 & m1 & evs1 & Hspec & Hcases).
    apply Hinv in Hspec. inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & Hr)].
    - left. mat_id Hm Hl. auto.
    - right. eauto.
  Qed.

  Lemma wstep_pending_run : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40A1M1S39S37G0S0S28G1A1M2S8R6A1S2aG1R4A2A3S0G2S3aR6A1S2fG1A1A3Sc8S1bVsegs;R8R6A3R7S98S39R5R4R3A4A3S77R5A1S79Vsegs;S27G0S1aRbS19RaR9A2A4S27G0S1aS32S36RbR5A3S19S1cS1dRaR7A2A1R6A2A4A3F_;F_;F_;F_;Fevs;Fm';Feff;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros. exists evs. split; [|reflexivity]. cbn. eapply sstep_pending_run; eauto.
  Qed.

  Lemma wstep_pending_exit : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40A1M1S39S37G0G1S0S28G1A1M2S8R7A1S2aG1R5A2A3S0G2S3aR7A1S2fG1A1M3A3S86S1bVsegs;R9R7A3R8S98S39R6R5R4A4A3S0G2S3aR6A1S2aG1R4A2A3S0G2S51R7A1G3A3S79Vsegs;S27G0S1aRdS19RcRbA2A4S27G0S1aS32S36RdS32S36R7S2eS36S4cR6S3fR8A1A2S2cS36A1A3A3A3S19RcR8A2A4A3F_;F_;F_;F_;F_;Fcode;Fevs;Fm';Feff;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros. exists (evs ++ [ExitEv code (m_fs m')]). split; [|cbn; now rewrite app_assoc].
    cbn. eapply sstep_pending_exit; eauto.
  Qed.

  Lemma wstep_retci_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40A1M1G1S29S2dG1S33A2A1S37G0S78S0S28G1A1M2S8R8A1S2aG1R6A2A3S0G2S3aR8A1S2fG1A1A3S99S39A1S86S1bVsegs;RbR9A3RaR1A3SacR2R9R8R7R6A5F_;FR;S77R6A1S79Vsegs;S27G0S1aRdS19RcRbA2A4R5A3S0S78R6S27G0S1aS32S36ReR7A3S19S7eRdRaA2R8A2A4A3F_;F_;F_;F_;F_;Fw';Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r ci m1 evs1 w' Hp Hh Hinv [Hh1 Hl1] Hw.
    destruct (wstep_pending_inv_idle Hp Hh Hw Hinv Hl1) as [(_ & ->) | (code & Hc & _)];
      [reflexivity | congruence].
  Qed.

  Lemma wstep_ret_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40A1M1G1S37G0S78S0S28G1A1M2S8R7A1S2aG1R5A2A3S0G2S3aR7A1S2fG1A1A3S99S39A1S86S1bVsegs;RaR8A3R9R1A3SadR2R8R7R6A4F_;FR;S77R6A1S79Vsegs;S27G0S1aRcS19RbRaA2A4R5A3S0S78R6S27G0S1aS32S36RdR7A3S19S7eRcR9A2R8A2A4A3F_;F_;F_;F_;F_;Fw';Fevs1;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r m1 evs1 w' Hp Hh Hinv Hi Hw.
    eapply wstep_retci_inv; eauto.
  Qed.

  Lemma wstep_retci_intro : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40A1M1G1S29S2dG1S33A2A1S37G0S0S28G1A1M2S8R7A1S2aG1R5A2A3S0G2S3aR7A1S2fG1A1A3Sc8S1bVsegs;R9R7A3R8S98S39S43R6S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M3G3S2cS40A1R5A6R4R3A4A3S77R5A1S79Vsegs;S27G0S1aRcS19RbRaA2A4S27G0S1aS32S36RcR5A3S19S7eRbR8A2R6A2A4A3F_;F_;F_;F_;Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r ci m1 evs1 Hp Hh Hs Hh1.
    rewrite <- (advance_apply_ret_ci ms r ci). eapply wstep_pending_run; eauto.
  Qed.

  Lemma wstep_ret_intro : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40A1M1G1S37G0S0S28G1A1M2S8R6A1S2aG1R4A2A3S0G2S3aR6A1S2fG1A1A3Sc8S1bVsegs;R8R6A3R7S98S39S43R5S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M3G3S2cS40A1S2cS2dG1S33A2A1A6R4R3A4A3S77R5A1S79Vsegs;S27G0S1aRbS19RaR9A2A4S27G0S1aS32S36RbR5A3S19S7eRaR7A2R6A2A4A3F_;F_;F_;F_;Fevs1;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using . intros. eapply wstep_retci_intro; eauto. Qed.

  Definition det_succ (w w1 : world) : Prop := ltac2:(tb__ "0|1|
S1S79Vsegs;Vw;Vw1;A3S1S78S79Vsegs;Vw;R1A3S0S78R2Vw1;A3F_;Fw';S1S29S36A1S2S1eVsegs;S7dVw;A1M0R1S20A4A1Fevs;S2S24Vsegs;G0A2A1A2A2A2").

  Lemma only_ok_retci : ltac2:(tb__ "0|1|
S7S37S15Q40A1M0G0S29S2dG0S33A2A1S37S29S36A1S99S39A1S86S1bVsegs;R8R6A3R7R1A3SacR2R6R5R4R3A5F_;FR;S77R3A1S87S1bVsegs;R9R7A3R8A2F_;F_;Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 r ci m1 evs1 Hinv [Hh1 Hl1].
    eapply only_ok_of_inv; [exact Hinv| unfold is_ret_ci; discriminate|].
    intros eff m' evs E _. unfold is_ret_ci in E. inversion E; subst. exact Hl1.
  Qed.

  Lemma only_ok_ret : ltac2:(tb__ "0|1|
S7S37S15Q40A1M0G0S37S29S36A1S99S39A1S86S1bVsegs;R7R5A3R6R1A3SadR2R5R4R3A4F_;FR;S77R3A1S87S1bVsegs;R8R6A3R7A2F_;F_;Fevs1;Fm1;Fr;Fx8;Fm;Fms;").
  Proof using . intros. eapply only_ok_retci; eauto. Qed.

  Lemma det_succ_retci : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40A1M1G1S29S2dG1S33A2A1S37G0S0S28G1A1M2S8R7A1S2aG1R5A2A3S0G2S3aR7A1S2fG1A1A3S99S39A1S86S1bVsegs;RaR8A3M3R9R1A3SacR2R8R7R6R5A5F_;FR;Sc8G3R9S98S39S43R7S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M4G4S2cS40A1R6A6R5R4A4A3S77R6A1S88S27G0S1aRdS19RcRbA2A4S27G0S1aS32S36RdR6A3S19S7eRcR9A2R7A2A4A2F_;F_;F_;F_;F_;Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r ci m1 evs1 Hp Hh Hinv Hs Hh1.
    pose proof (@only_ok_retci ms m x8 r ci m1 evs1 Hinv Hh1) as Hok.
    split; [exact (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp Hh Hs Hh1)|].
    split; [intros w' Hw; exact (@wstep_retci_inv _ _ _ _ _ _ _ _ _ Hp Hh Hinv Hh1 Hw)|].
    split; [intros evs; exact (pending_no_error (evs:=evs) Hp Hok)|].
    exact (pending_not_unmodeled_at Hp Hok).
  Qed.

  Lemma det_succ_ret : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40A1M1G1S37G0S0S28G1A1M2S8R6A1S2aG1R4A2A3S0G2S3aR6A1S2fG1A1A3S99S39A1S86S1bVsegs;R9R7A3M3R8R1A3SadR2R7R6R5A4F_;FR;Sc8G3R8S98S39S43R6S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M4G4S2cS40A1S2cS2dG1S33A2A1A6R5R4A4A3S77R6A1S88S27G0S1aRcS19RbRaA2A4S27G0S1aS32S36RcR6A3S19S7eRbR8A2R7A2A4A2F_;F_;F_;F_;F_;Fevs1;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using . intros. eapply det_succ_retci; eauto. Qed.

  Lemma wstep_pending_run0 : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40A1M1S39S37S0S28G1A1M2S8R5A1S2aG1R3A2A3S0G2S3aR5A1S2fG1A1A3Sc8S1bVsegs;R7R5A3R6S98S39R4R3S2cS36A1A4A3S77R4A1S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S1cS1dR9R6A2A1R5A2A4A3F_;F_;F_;F_;Fm';Feff;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros. exists []. split; [cbn; eapply sstep_pending_run; eauto | cbn; now rewrite app_nil_r].
  Qed.

  Lemma wstep_retci_inv0 : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40A1M1G1S29S2dG1S33A2A1S37S78S0S28G1A1M2S8R7A1S2aG1R5A2A3S0G2S3aR7A1S2fG1A1A3S99S39A1S86S1bVsegs;RaR8A3R9R1A3SacR2R8R7R6S2cS36A1A5F_;FR;S77R5A1S79Vsegs;S27G0S1aRcS19RbRaA2A4R5A3S0S78R6S27G0S1aRdS19S7eRcR9A2R7A2A4A3F_;F_;F_;F_;F_;Fw';Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r ci m1 w' Hp Hh Hinv Hh1 Hw.
    rewrite (@wstep_retci_inv _ _ _ _ _ _ _ _ _ Hp Hh Hinv Hh1 Hw). now rewrite app_nil_r.
  Qed.

  Lemma wstep_ret_inv0 : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40A1M1G1S37S78S0S28G1A1M2S8R6A1S2aG1R4A2A3S0G2S3aR6A1S2fG1A1A3S99S39A1S86S1bVsegs;R9R7A3R8R1A3SadR2R7R6S2cS36A1A4F_;FR;S77R5A1S79Vsegs;S27G0S1aRbS19RaR9A2A4R5A3S0S78R6S27G0S1aRcS19S7eRbR8A2R7A2A4A3F_;F_;F_;F_;F_;Fw';Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using . intros. eapply wstep_retci_inv0; eauto. Qed.

  Lemma wstep_retci_intro0 : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40A1M1G1S29S2dG1S33A2A1S37S0S28G1A1M2S8R6A1S2aG1R4A2A3S0G2S3aR6A1S2fG1A1A3Sc8S1bVsegs;R8R6A3R7S98S39S43R5S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M3G3S2cS40A1R4A6R3S2cS36A1A4A3S77R4A1S79Vsegs;S27G0S1aRbS19RaR9A2A4S27G0S1aRbS19S7eRaR7A2R5A2A4A3F_;F_;F_;F_;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r ci m1 Hp Hh Hs Hh1.
    rewrite <- (advance_apply_ret_ci ms r ci). eapply wstep_pending_run0; eauto.
  Qed.

  Lemma wstep_ret_intro0 : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40A1M1G1S37S0S28G1A1M2S8R5A1S2aG1R3A2A3S0G2S3aR5A1S2fG1A1A3Sc8S1bVsegs;R7R5A3R6S98S39S43R4S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M3G3S2cS40A1S2cS2dG1S33A2A1A6R3S2cS36A1A4A3S77R4A1S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7eR9R6A2R5A2A4A3F_;F_;F_;F_;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using . intros. eapply wstep_retci_intro0; eauto. Qed.

  Lemma det_succ_retci0 : ltac2:(tb__ "0|6|
S29S36A1M0S7S37S15Q40A1M1G1S29S2dG1S33A2A1S37S0S28G1A1M2S8R6A1S2aG1R4A2A3S0G2S3aR6A1S2fG1A1A3S99S39A1S86S1bVsegs;R9R7A3M3R8R1A3SacR2R7R6R5S2cS36A1M4A5F_;FR;Sc8G3R8S98S39S43R6S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M5G5S2cS40A1R5A6R4G4A4A3S77R5A1S88S27G0S1aRcS19RbRaA2A4S27G0S1aRcS19S7eRbR8A2R6A2A4A2F_;F_;F_;F_;F_;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r ci m1 Hp Hh Hinv Hs Hh1.
    pose proof (@det_succ_retci tr _ _ _ _ _ _ _ Hp Hh Hinv Hs Hh1) as D. rewrite app_nil_r in D. exact D.
  Qed.

  Lemma det_succ_ret0 : ltac2:(tb__ "0|6|
S29S36A1M0S7S37S15Q40A1M1G1S37S0S28G1A1M2S8R5A1S2aG1R3A2A3S0G2S3aR5A1S2fG1A1A3S99S39A1S86S1bVsegs;R8R6A3M3R7R1A3SadR2R6R5S2cS36A1M4A4F_;FR;Sc8G3R7S98S39S43R5S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M5G5S2cS40A1S2cS2dG1S33A2A1A6R4G4A4A3S77R5A1S88S27G0S1aRbS19RaR9A2A4S27G0S1aRbS19S7eRaR7A2R6A2A4A2F_;F_;F_;F_;F_;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using . intros. eapply det_succ_retci0; eauto. Qed.

  Definition exit_code (ms : machine_state) : word := bv_and (ms_gpr ms 0) (Z_to_bv 64 255).
  Definition exited (ms : machine_state) (m : Model) : Model := with_halted (exit_code ms) m.

  Lemma wstep_exit_inv : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1M3S8R4A1S2aG2R2A2A3S0G3S3aR4A1S2fG2A1A3S3S0S76S16G1R4A2M4Z5dA3S0S76G4Z5eA3A2S79Vsegs;S27G0S1aR8S19R7R6A2A4R4A3S0S78R5S27G0S1aS32S36R9S2eS36S4cS8cR8A1S3fR7A1A2S2cS36A1A3A3S19R8S89R8R7A2A2A4A3F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp Hh Hno Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (exit_inv (sys_input segs ms x8) m _ Hno) in Hspec. unfold is_ret in Hspec.
    inversion Hspec; subst.
    destruct Hcases as [(Hh' & _) | (code & Hc & [(_ & ->) | (Hk & _)])].
    - cbn in Hh'. discriminate.
    - cbn in Hc. inversion Hc; subst. reflexivity.
    - exfalso. revert Hk. unfold exit_model. rewrite m_killed_with_halted. discriminate.
  Qed.

  Lemma wstep_exit_intro : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1M3S8R3A1S2aG2R1A2A3S0G3S3aR3A1S2fG2A1A3S3S0S76S16G1R3A2M4Z5dA3S0S76G4Z5eA3A2S79Vsegs;S27G0S1aR7S19R6R5A2A4S27G0S1aS32S36R7S2eS36S4cS8cR6A1S3fR5A1A2S2cS36A1A3A3S19R6S89R6R5A2A2A4A3F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hh Hno.
    pose proof (@wstep_pending_exit tr ms m x8 _ _ _ (exit_code ms) Hp Hh
                  (exit_intro (sys_input segs ms x8) m Hno) eq_refl
                  (m_killed_with_halted _ _)) as W.
    exact W.
  Qed.

  Lemma exit_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1S3S0S76S16G0R1A2M1Z5dA3S0S76G1Z5eA3A2S87S1bVsegs;R4R2A3R3A2F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 Hno. eapply only_ok_of_inv; [intros R; apply exit_inv; exact Hno| |].
    - unfold is_ret. discriminate.
    - intros eff m' evs E Hh'. unfold is_ret in E. inversion E; subst. cbn in Hh'. discriminate.
  Qed.

  Lemma exited_halted : ltac2:(tb__ "0|1|
S7S37S0S28S15Q40A1M0A1S3aS89R2R1A2A1S2aG0S8cR2A1A2A3Fm;Fms;").
  Proof using . reflexivity. Qed.
  Lemma exited_fs : ltac2:(tb__ "0|0|
S7S37S0Sa1S3fS89R2R1A2A1S3fR1A1A3Fm;Fms;").
  Proof using . reflexivity. Qed.

  Lemma wstep_exited_none : ltac2:(tb__ "0|1|
S29S36A1M0S7S7S37S78S2S79Vsegs;S27G0S1aR5S19R3S89R4R2A2A2A4R1A3A1Fw';Fm;Fms';Fms;Ftr;").
  Proof using . intros. eapply halted_no_wstep. apply exited_halted. Qed.

  Lemma wstep_write_inv : ltac2:(tb__ "0|8|
S29S36A1M0S7S37S15Q40M1A1M2G2S29S15Q8A1M3A1M4S78S0S28G2A1S8R6A1S2aG2R4A2A3S77R6A1S0S76S16G1R6A2Z40A3S0S28S38A1S3dS3bR8A1S84S6R9U0A2A1A2S2aS38S49R6A1A2A3S2S0G2R7S17G1Z0M5A2A3A1S0S28G4A1S4eS9RbA1S6RbU1M6A2S6RbU2M7A2A3S2aG4R7A2A3S8fG5S16G1S6RcG7A2A2A2S8dS16G1S6RdG7A2A2SbdA2S79Vsegs;S27G0S1aRfS19ReRdA2A4R9A3S4S33S33S1S1SbcG6R1A2SbcR1S34G3RcA2A2A2S0S78RbS27G0S1aS32S36R11Sc0G3S36S5eRdA1Sc1G3R1RcA3A4A3S19S7eR10S17G1S92R1A1A2A2RfA2A4A3A2Lk;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fbs;Fch;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 ch bs w' Hp [Hh Hl] Hno Hfd Hch Hbuf Hpos Hmax Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@write_inv (sys_input segs ms x8) m ch bs Hno Hfd Hch Hbuf Hpos Hmax) in Hspec.
    destruct Hspec as (k & Hk & E). unfold is_ret_ci in E. inversion E; subst.
    exists k. split; [exact Hk|].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    mat_id Hm Hl. reflexivity.
  Qed.

  Lemma wstep_write_intro_prefix : ltac2:(tb__ "0|8|
S29S36A1M0S7S37S15Q40M1A1M2G2S29S15Q8A1M3A1M4S33S0S28G2A1S8R6A1S2aG2R4A2A3S77R6A1S0S76S16G1R6A2Z40A3S0S28S38A1S3dS3bR8A1S84S6R9U0A2A1A2S2aS38S49R6A1A2A3S2S0G2R7S17G1Z0M5A2A3A1S0S28G4A1S4eS9RbA1S6RbU1M6A2S6RbU2M7A2A3S2aG4R7A2A3S8fG5S16G1S6RcG7A2A2A2S8dS16G1S6RdG7A2A2SbdA2S1SbcG6R9A2SbcR9S34G3RaA2A2A2S79Vsegs;S27G0S1aR10S19RfReA2A4S27G0S1aS32S36R10Sc0G3S36S5eRcA1Sc1G3RaRbA3A4A3S19S7eRfS17G1S92RaA1A2A2ReA2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fk;Fbs;Fch;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 ch bs k Hp Hi Hno Hfd Hch Hbuf Hpos Hmax Hk.
    refine (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@write_intro_prefix (sys_input segs ms x8) m ch bs Hno Hfd Hch Hbuf Hpos Hmax k Hk).
  Qed.

  Lemma wstep_write_intro : ltac2:(tb__ "0|7|
S29S36A1M0S7S37S15Q40M1A1M2G2S29S15Q8A1M3A1M4S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z40A3S0S28S38A1S3dS3bR7A1S84S6R8U0A2A1A2S2aS38S49R5A1A2A3S2S0G2R6S17G1Z0M5A2A3A1S0S28G4A1S4eS9RaA1S6RaU1A2S6RaU2M6A2A3S2aG4R6A2A3S8fG5S16G1S6RbG6A2A2A2S8dS16G1S6RcG6A2A2SbdA2S79Vsegs;S27G0S1aReS19RdRcA2A4S27G0S1aS32S36ReSc0G3S36S5eRaA1R9A4A3S19S7eRdS6RdG6A2A2RcA2A4A3F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fch;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 ch bs Hp Hi Hno Hfd Hch Hbuf Hpos Hmax.
    refine (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@write_intro (sys_input segs ms x8) m ch bs Hno Hfd Hch Hbuf Hpos Hmax).
  Qed.

  Lemma write_only_ok : ltac2:(tb__ "0|5|
S7S37S15Q40M0A1M1G1S29S15Q8A1A1M2S77R4A1S0S76S16G0R4A2Z40A3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2aS38S49R4A1A2A3S2S0G1R5S17G0Z0M3A2A3A1S0S28G2A1S4eS9R9A1S6R9U1A2S6R9U2M4A2A3S2aG2R5A2A3S8fG3S16G0S6RaG4A2A2A2S8dS16G0S6RbG4A2A2SbdA2S87S1bVsegs;RcRaA3RbA2F_;F_;F_;F_;F_;F_;F_;Fbs;Fch;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 ch bs [Hh Hl] Hno Hfd Hch Hbuf Hpos Hmax.
    eapply only_ok_of_inv;
      [intros R; exact (@write_inv (sys_input segs ms x8) m ch bs Hno Hfd Hch Hbuf Hpos Hmax R)| |].
    - intros (k & _ & E). unfold is_ret_ci in E. discriminate.
    - intros eff m' evs (k & _ & E) _. unfold is_ret_ci in E. inversion E; subst. exact Hl.
  Qed.

  Definition closed_model (ms : machine_state) (m : Model) : Model := ltac2:(tb__ "0|0|
S58S70S3bVm;A1S84S6Vms;U0A2A1A2Vm;A2").

  Lemma closed_model_idle : ltac2:(tb__ "0|0|
S7S37S77R1A1S77S8bR3R2A2A1F_;Fm;Fms;").
  Proof using . intros ms m [H1 H2]. split; assumption. Qed.

  Lemma wstep_close_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S38S78S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z39A3S0S28S38A1S3dS3bR7A1S84S6R8U0A2A1A2S2aS38R5A2A3S79Vsegs;S27G0S1aRaS19R9R8A2A4R5A3S0S78R6S27G0S1aRbS19S7eRaS17G1Z0A2A2S8bRaR9A2A2A4A3F_;F_;F_;F_;F_;Fw';Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e w' Hp Hi Hno Hfd Hw.
    refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ (closed_model_idle ms Hi) Hw).
    intros R. exact (@close_inv (sys_input segs ms x8) m Hno e R Hfd).
  Qed.

  Lemma wstep_close_intro : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S38S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z39A3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2aS38R4A2A3S79Vsegs;S27G0S1aR9S19R8R7A2A4S27G0S1aR9S19S7eR8S17G1Z0A2A2S8bR8R7A2A2A4A3F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hi Hno Hfd.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ (closed_model_idle ms Hi)).
    exact (@close_intro (sys_input segs ms x8) m Hno e Hfd).
  Qed.

  Lemma close_only_ok : ltac2:(tb__ "0|1|
S7S37S15Q40M0A1S38S77R3A1S0S76S16G0R3A2Z39A3S0S28S38A1S3dS3bR5A1S84S6R6U0A2A1A2S2aS38R3A2A3S87S1bVsegs;R7R5A3R6A2F_;F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e Hi Hno Hfd.
    eapply only_ok_ret; [intros R; exact (@close_inv (sys_input segs ms x8) m Hno e R Hfd)|].
    exact (closed_model_idle ms Hi).
  Qed.

  Lemma det_succ_close : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S38S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z39A3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2aS38R4A2A3S88S27G0S1aR9S19R8R7A2A4S27G0S1aR9S19S7eR8S17G1Z0A2A2S8bR8R7A2A2A4A2F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hi Hno Hfd.
    refine (@det_succ_ret0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ _ (closed_model_idle ms Hi)).
    - intros R. exact (@close_inv (sys_input segs ms x8) m Hno e R Hfd).
    - exact (@close_intro (sys_input segs ms x8) m Hno e Hfd).
  Qed.

  Lemma wstep_close_absent_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z39A3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2fS38A1A3S79Vsegs;S27G0S1aR9S19R8R7A2A4R5A3S0S78R6S27G0S1aRaS19S7eR9S3cS63A1A2R8A2A4A3F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp Hi Hno Hfd Hw.
    refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. exact (@close_absent_inv (sys_input segs ms x8) m Hno R Hfd).
  Qed.

  Lemma wstep_close_absent_intro : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2Z39A3S0S28S38A1S3dS3bR5A1S84S6R6U0A2A1A2S2fS38A1A3S79Vsegs;S27G0S1aR8S19R7R6A2A4S27G0S1aR8S19S7eR7S3cS63A1A2R6A2A4A3F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hfd.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@close_absent_intro (sys_input segs ms x8) m Hno Hfd).
  Qed.

  Lemma wstep_ioctl_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2G2S78S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z1dA3S0S28S38A1S3dS3bR7A1S84S6R8U0A2A1A2S2aS38S49R5A1A2A3S0G2S85S6R9U1A2A1S9cA3S79Vsegs;S27G0S1aRbS19RaR9A2A4R6A3S0S78R7S27G0S1aRcS19S7eRbS3cS5aA1A2RaA2A4A3F_;F_;F_;F_;F_;F_;Fw';Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e w' Hp Hi Hno Hfd Hc Hw.
    refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. exact (@ioctl_inv (sys_input segs ms x8) m Hno e R Hfd Hc).
  Qed.

  Lemma wstep_ioctl_intro : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2G2S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z1dA3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2aS38S49R4A1A2A3S0G2S85S6R8U1A2A1S9cA3S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7eR9S3cS5aA1A2R8A2A4A3F_;F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hi Hno Hfd Hc.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@ioctl_intro (sys_input segs ms x8) m Hno e Hfd Hc).
  Qed.

  Lemma ioctl_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1M1G1S77R3A1S0S76S16G0R3A2Z1dA3S0S28S38A1S3dS3bR5A1S84S6R6U0A2A1A2S2aS38S49R3A1A2A3S0G1S85S6R7U1A2A1S9cA3S87S1bVsegs;R8R6A3R7A2F_;F_;F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e Hi Hno Hfd Hc.
    eapply only_ok_ret; [intros R; exact (@ioctl_inv (sys_input segs ms x8) m Hno e R Hfd Hc)| exact Hi].
  Qed.

  Lemma det_succ_ioctl : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2G2S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z1dA3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2aS38S49R4A1A2A3S0G2S85S6R8U1A2A1S9cA3S88S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7eR9S3cS5aA1A2R8A2A4A2F_;F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hi Hno Hfd Hc.
    refine (@det_succ_ret0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ _ Hi).
    - intros R. exact (@ioctl_inv (sys_input segs ms x8) m Hno e R Hfd Hc).
    - exact (@ioctl_intro (sys_input segs ms x8) m Hno e Hfd Hc).
  Qed.

  Lemma with_tid_idle : ltac2:(tb__ "0|0|
S15Q40A1S37S77R1A1S77S62R3R2A2A1F_;Fm;Ft;").
  Proof using . intros t m [H1 H2]. split; assumption. Qed.

  Lemma wstep_set_tid_fresh_inv : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1M3S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z60A3S0G3S52R6A1S2fG2A1A3S79Vsegs;S27G0S1aR9S19R8R7A2A4R5A3S4G2G2S1S1S8fZ0S16G1R1A2M4A2S8fG4Sc2A2A2S0S78R7S27G0S1aRbS19S7eRaR1A2S62R1R9A2A2A4A3A2Ltid;A2F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Ht Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (set_tid_fresh_inv (sys_input segs ms x8) m Hno _ Ht) in Hspec.
    destruct Hspec as (tid & Hr & E). unfold is_ret in E. inversion E; subst.
    exists tid. split; [exact Hr|].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)].
    - mat_id Hm Hl. now rewrite app_nil_r.
    - msimp Hc. congruence.
  Qed.

  Lemma wstep_set_tid_fresh_intro : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2G2S0S28G2A1M3S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z60A3S0G3S52R6A1S2fG2A1A3S1S8fZ0S16G1R5A2M4A2S8fG4Sc2A2A2S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7eR9R6A2S62R6R8A2A2A4A3F_;F_;F_;F_;F_;Ftid;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 tid Hp Hi Hno Ht Hr.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ (with_tid_idle tid Hi)).
    exact (set_tid_fresh_intro (sys_input segs ms x8) m Hno tid Ht Hr).
  Qed.

  Lemma tid_one_ok : ltac2:(tb__ "0|2|
S1S8fZ0S16Q40M0S17G0Z1A2A2M1A2S8fG1Sc2A2A2").
  Proof using . vm_compute. split; reflexivity. Qed.

  Lemma set_tid_fresh_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1M1S77R2A1S0S76S16G0R2A2Z60A3S0S28G1A1S52R4A1S2fG1A1A3S87S1bVsegs;R6R4A3R5A2F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 [Hh Hl] Hno Ht.
    eapply only_ok_of_inv;
      [intros R; exact (set_tid_fresh_inv (sys_input segs ms x8) m Hno R Ht)| |].
    - intros (tid & _ & E). unfold is_ret in E. discriminate.
    - intros eff m' evs (tid & _ & E) _. unfold is_ret in E. inversion E; subst. exact Hl.
  Qed.

  Lemma wstep_set_tid_known_inv : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40M1A1M2G2S78S0S28G2A1M3S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z60A3S0G3S52R7A1S2aG2R5A2A3S79Vsegs;S27G0S1aRaS19R9R8A2A4R5A3S0S78R6S27G0S1aRbS19S7eRaR7A2R9A2A4A3F_;F_;F_;F_;F_;Fw';Ft;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 t w' Hp Hi Hno Ht Hw.
    refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. exact (set_tid_known_inv (sys_input segs ms x8) m Hno t R Ht).
  Qed.

  Lemma wstep_set_tid_known_intro : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40M1A1M2G2S0S28G2A1M3S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z60A3S0G3S52R6A1S2aG2R4A2A3S79Vsegs;S27G0S1aR9S19R8R7A2A4S27G0S1aR9S19S7eR8R5A2R7A2A4A3F_;F_;F_;F_;Ft;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 t Hp Hi Hno Ht.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (set_tid_known_intro (sys_input segs ms x8) m Hno t Ht).
  Qed.

  Lemma set_tid_known_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1M1G1S77R3A1S0S76S16G0R3A2Z60A3S0S28G1A1S52R5A1S2aG1R3A2A3S87S1bVsegs;R7R5A3R6A2F_;F_;F_;Ft;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 t Hi Hno Ht.
    eapply only_ok_ret; [intros R; exact (set_tid_known_inv (sys_input segs ms x8) m Hno t R Ht)| exact Hi].
  Qed.

  Lemma wstep_writev2_inv : forall tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 w',
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    wstep (tr, mkCfg ms m) w' ->
    exists k, (1 <= k <= length (bs1 ++ bs2))%nat
      /\ w' = (tr ++ map (WriteEv ch) (firstn k (bs1 ++ bs2)), mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) m).
  Proof using .
    intros tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 w' Hp [Hh Hl] Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@writev2_inv (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2
             Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen) in Hspec.
    destruct Hspec as (k & Hk & E). unfold is_ret_ci in E. inversion E; subst.
    exists k. split; [exact Hk|].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    mat_id Hm Hl. reflexivity.
  Qed.

  Lemma wstep_writev2_intro_prefix : forall tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 k,
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    (1 <= k <= length (bs1 ++ bs2))%nat ->
    wstep (tr, mkCfg ms m)
          (tr ++ map (WriteEv ch) (firstn k (bs1 ++ bs2)), mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) m).
  Proof using .
    intros tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 k Hp Hi Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen Hk.
    refine (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@writev2_intro_prefix (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2
             Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen k Hk).
  Qed.

  Lemma wstep_writev2_intro : forall tr ms m x8 ch b1 l1 b2 l2 bs1 bs2,
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    wstep (tr, mkCfg ms m)
          (tr ++ map (WriteEv ch) (bs1 ++ bs2), mkCfg (after_sys ms (len_word (bs1 ++ bs2))) m).
  Proof using .
    intros tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 Hp Hi Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen.
    refine (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@writev2_intro (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2
             Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen).
  Qed.

  Lemma writev2_only_ok : forall ms m x8 ch b1 l1 b2 l2 bs1 bs2,
    model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    only_ok (sys_input segs ms x8) m.
  Proof using .
    intros ms m x8 ch b1 l1 b2 l2 bs1 bs2 [Hh Hl] Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen.
    eapply only_ok_of_inv;
      [intros R; exact (@writev2_inv (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2
                          Hno Hfd Hch Hcnt H1 H2 H3 H4 Hb1 Hb2 Hiok Hok1 Hok2 Hlen R)| |].
    - intros (k & _ & E). unfold is_ret_ci in E. discriminate.
    - intros eff m' evs (k & _ & E) _. unfold is_ret_ci in E. inversion E; subst. exact Hl.
  Qed.

  Lemma wstep_writev1_inv : forall tr ms m x8 ch b1 l1 bs1 w',
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    wstep (tr, mkCfg ms m) w' ->
    exists k, (1 <= k <= length bs1)%nat
      /\ w' = (tr ++ map (WriteEv ch) (firstn k bs1), mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) m).
  Proof using .
    intros tr ms m x8 ch b1 l1 bs1 w' Hp [Hh Hl] Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@writev1_inv (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen) in Hspec.
    destruct Hspec as (k & Hk & E). unfold is_ret_ci in E. inversion E; subst.
    exists k. split; [exact Hk|].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    mat_id Hm Hl. reflexivity.
  Qed.

  Lemma wstep_writev1_intro_prefix : forall tr ms m x8 ch b1 l1 bs1 k,
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    (1 <= k <= length bs1)%nat ->
    wstep (tr, mkCfg ms m)
          (tr ++ map (WriteEv ch) (firstn k bs1), mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) m).
  Proof using .
    intros tr ms m x8 ch b1 l1 bs1 k Hp Hi Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen Hk.
    refine (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@writev1_intro_prefix (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen k Hk).
  Qed.

  Lemma wstep_writev1_intro : forall tr ms m x8 ch b1 l1 bs1,
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    wstep (tr, mkCfg ms m)
          (tr ++ map (WriteEv ch) bs1, mkCfg (after_sys ms (len_word bs1)) m).
  Proof using .
    intros tr ms m x8 ch b1 l1 bs1 Hp Hi Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen.
    refine (@wstep_retci_intro tr _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@writev1_intro (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen).
  Qed.

  Lemma writev1_only_ok : forall ms m x8 ch b1 l1 bs1,
    model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    only_ok (sys_input segs ms x8) m.
  Proof using .
    intros ms m x8 ch b1 l1 bs1 [Hh Hl] Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen.
    eapply only_ok_of_inv;
      [intros R; exact (@writev1_inv (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt H1 H2 Hb1 Hiok Hok1 Hlen R)| |].
    - intros (k & _ & E). unfold is_ret_ci in E. discriminate.
    - intros eff m' evs (k & _ & E) _. unfold is_ret_ci in E. inversion E; subst. exact Hl.
  Qed.

  Lemma with_fds_idle : ltac2:(tb__ "0|0|
S29S2dS15Q40A1S38A2A1S37S77R1A1S77S58R3R2A2A1F_;Fm;Ff;").
  Proof using . intros f m [H1 H2]. split; assumption. Qed.

  Lemma rd_access_ok : ltac2:(tb__ "0|3|
S15Q40M0A1M1G1S8dS90S16G0R2A2M2S16G0R1A2A2S4aA2S0S2bS69R3G2A2S30A3F_;Fcount;Fbuf;").
  Proof using . intros buf count H. apply access_okb_intro. exact H. Qed.

  Lemma wstep_read_file_inv : ltac2:(tb__ "0|b|
S29S36A1M0S7S37S15Q40M1A1M2S9fG2S29S15Q8A1M3A1M4G4S78S0S28G2A1S8R8A1S2aG2R6A2A3S77R8A1S0S76S16G1R8A2Z3fA3S0S28S38A1S3dS3bRaA1S84S6RbU0M5A2A1A2S2aS38S55R8R7A2A2A3S0S28G4A1M6S9eS3fRbA1R9A2S2aG4R7A2M7A3S0G6S4eSdVsegs;RdA2S6RdU1M8A2S6RdU2M9A2A3G7A3S8dS16G1S6ReG9A2A2S5dA2S8dS90S16G1S6RfG8A2A2S16G1S6RfG9A2A2A2S4aA2Sa0RbRcS6R10G9A2A3G4S79Vsegs;S27G0S1aR12S19R11R10A2A4RaA3S0S78RbS27G0S1aR13S19S7fR12Sc5G3R2A2MaSeSaR12A1S6R12G8A2R2A3A3S58S65S3bR11A1S84S6R12G5A2A1S55RfS18G1ReGaA3A2A3R11A2A2A4A3F_;Tbs;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fwdst;Fdata;Foff;Fp;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 p off data wdst w' Hp [Hh Hl] Hno Hfd Hfs Hw Hcnt Hov bs Hst.
    destruct (wstep_pending_inv Hp Hh Hst) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@read_file_inv (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov)) in Hspec.
    inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|msimp Hc; congruence].
    mat_id Hm Hl.
    unfold read_file_eff. rewrite advance_apply_delivered, app_nil_r. reflexivity.
  Qed.

  Lemma wstep_read_file_intro : ltac2:(tb__ "0|b|
S29S36A1M0S7S37S15Q40M1A1M2S9fG2S29S15Q8A1M3A1M4G4S0S28G2A1S8R7A1S2aG2R5A2A3S77R7A1S0S76S16G1R7A2Z3fA3S0S28S38A1S3dS3bR9A1S84S6RaU0M5A2A1A2S2aS38S55R7R6A2A2A3S0S28G4A1M6S9eS3fRaA1R8A2S2aG4R6A2M7A3S0G6S4eSdVsegs;RcA2S6RcU1M8A2S6RcU2M9A2A3G7A3S8dS16G1S6RdG9A2A2S5dA2S8dS90S16G1S6ReG8A2A2S16G1S6ReG9A2A2A2S4aA2Sa0RaRbS6RfG9A2A3G4S79Vsegs;S27G0S1aR11S19R10RfA2A4S27G0S1aR11S19S7fR10Sc5G3R1A2MaSeSaR10A1S6R10G8A2R1A3A3S58S65S3bRfA1S84S6R10G5A2A1S55RdS18G1RcGaA3A2A3RfA2A2A4A3Tbs;F_;F_;F_;F_;F_;F_;F_;F_;Fwdst;Fdata;Foff;Fp;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 p off data wdst Hp Hi Hno Hfd Hfs Hw Hcnt Hov bs.
    pose proof (@read_file_intro (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov)) as Hs.
    pose proof (@wstep_pending_run0 tr _ _ _ _ _ Hp (model_idle_halted Hi) Hs (with_fds_idle _ Hi)) as W.
    unfold read_file_eff in W. rewrite advance_apply_delivered in W. exact W.
  Qed.

  Lemma read_file_only_ok : ltac2:(tb__ "0|7|
S7S37S15Q40M0A1M1S9fG1S29S15Q8A1A1M2G2S77R6A1S0S76S16G0R6A2Z3fA3S0S28S38A1S3dS3bR8A1S84S6R9U0A2A1A2S2aS38S55R6R5A2A2A3S0S28G2A1M3S9eS3fR9A1R7A2S2aG2R5A2M4A3S0G3S4eSdVsegs;RbA2S6RbU1M5A2S6RbU2M6A2A3G4A3S8dS16G0S6RcG6A2A2S5dA2S8dS90S16G0S6RdG5A2A2S16G0S6RdG6A2A2A2S4aA2S87S1bVsegs;ReRcA3RdA2F_;F_;F_;F_;F_;F_;F_;Fwdst;Fdata;Foff;Fp;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 p off data wdst [Hh Hl] Hno Hfd Hfs Hw Hcnt Hov.
    eapply only_ok_of_inv;
      [intros R; exact (@read_file_inv (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov) R)| |].
    - discriminate.
    - intros eff m' evs E _. inversion E; subst. exact Hl.
  Qed.

  Lemma wstep_read_dir_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z3fA3S0S28S38A1S3dS3bR6A1S84S6R7U0A2A1A2S2aS38S5bA2A3S8dS90S16G1S6R8U1A2A2S16G1S6R8U2A2A2A2S4aA2S79Vsegs;S27G0S1aRaS19R9R8A2A4R6A3S0S78R7S27G0S1aRbS19S7eRaS3cS64A1A2R9A2A4A3F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp Hi Hno Hfd Hov Hst.
    refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hst).
    intros R. exact (@read_dir_inv (sys_input segs ms x8) m Hno Hfd (rd_access_ok _ _ Hov) R).
  Qed.

  Lemma wstep_read_dir_intro : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2Z3fA3S0S28S38A1S3dS3bR5A1S84S6R6U0A2A1A2S2aS38S5bA2A3S8dS90S16G1S6R7U1A2A2S16G1S6R7U2A2A2A2S4aA2S79Vsegs;S27G0S1aR9S19R8R7A2A4S27G0S1aR9S19S7eR8S3cS64A1A2R7A2A4A3F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hfd Hov.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@read_dir_intro (sys_input segs ms x8) m Hno Hfd (rd_access_ok _ _ Hov)).
  Qed.

  Lemma read_dir_only_ok : ltac2:(tb__ "0|1|
S7S37S15Q40M0A1S77R2A1S0S76S16G0R2A2Z3fA3S0S28S38A1S3dS3bR4A1S84S6R5U0A2A1A2S2aS38S5bA2A3S8dS90S16G0S6R6U1A2A2S16G0S6R6U2A2A2A2S4aA2S87S1bVsegs;R7R5A3R6A2F_;F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 Hi Hno Hfd Hov.
    eapply only_ok_ret; [intros R; exact (@read_dir_inv (sys_input segs ms x8) m Hno Hfd (rd_access_ok _ _ Hov) R)| exact Hi].
  Qed.

  Lemma wstep_openat_file_inv : ltac2:(tb__ "0|7|
S29S36A1M0S7S37S15Q40M1A1M2S15Q8A1M3S29G3A1M4G4S78S0S28G2A1S8R7A1S2aG2R5A2A3S77R7A1S0S76S16G1R7A2Z38A3S0S76S8eS16G1S6RaU2A2A2S95A2Z0A3S0G2S84S6RbU0A2A1S9bA3S0S42S3eS9RcA1S6RcU1A2A2S44S2eG3R9R8A3A1A3S0S2bS96S2eG3RaR9A3A1S31A3S0S2bSbaS2eG3RbRaA3A1S31A3S0S28G4A1S9eS3fReA1S2eG3RcRbA3A2S2aG4RaA2A3S79Vsegs;S27G0S1aR11S19R10RfA2A4RaA3S3S4S76S76S1SbbS76R1S97A3S0S78RcS27G0S1aR13S19S7eR12S3cR1A1A2R11A2A4A3A2Le;A2S1S0S28S38A1S3dS3bR10A1M5S48G5A1M6A2S2fS38A1A3S0S78RbS27G0S1aR12S19S7eR11G6A2Sb8R10S2eG3ReRdA3A2A2A4A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fdata;Fp;Fb;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 b p data w' Hp [Hh Hl] Hno Hfl Hdir Hc Hnd Hsl Hfs Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@openat_file_inv (sys_input segs ms x8) m Hno Hfl Hdir _ b p data Hc Hnd Hsl Hfs) in Hspec.
    destruct Hspec as [(e & Hin & E) | (Hfree & E)]; unfold is_ret_ci in E; inversion E; subst.
    - left. exists e. split; [exact Hin|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. split; [exact Hfree|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  Lemma wstep_openat_file_intro_ok : ltac2:(tb__ "0|6|
S29S36A1M0S7S37S15Q40M1A1M2S15Q8A1M3S29G3A1M4G4S0S28G2A1S8R6A1S2aG2R4A2A3S77R6A1S0S76S16G1R6A2Z38A3S0S76S8eS16G1S6R9U2A2A2S95A2Z0A3S0G2S84S6RaU0A2A1S9bA3S0S42S3eS9RbA1S6RbU1A2A2S44S2eG3R8R7A3A1A3S0S2bS96S2eG3R9R8A3A1S31A3S0S2bSbaS2eG3RaR9A3A1S31A3S0S28G4A1S9eS3fRdA1S2eG3RbRaA3A2S2aG4R9A2A3S0S28S38A1S3dS3bReA1M5S48G5A1A2S2fS38A1A3S79Vsegs;S27G0S1aR11S19R10RfA2A4S27G0S1aR11S19S7eR10S48S3bRfA1A1A2Sb8RfS2eG3RdRcA3A2A2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fdata;Fp;Fb;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 b p data Hp Hi Hno Hfl Hdir Hc Hnd Hsl Hfs Hfree.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ (with_fds_idle _ Hi)).
    exact (@openat_file_intro_ok (sys_input segs ms x8) m Hno Hfl Hdir b p data Hc Hnd Hsl Hfs Hfree).
  Qed.

  Lemma wstep_openat_file_intro_err : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S15Q8A1M3S29G3A1M4G4S76S0S28G2A1S8R7A1S2aG2R5A2A3S77R7A1S0S76S16G1R7A2Z38A3S0S76S8eS16G1S6RaU2A2A2S95A2Z0A3S0G2S84S6RbU0A2A1S9bA3S0S42S3eS9RcA1S6RcU1A2A2S44S2eG3R9R8A3A1A3S0S2bS96S2eG3RaR9A3A1S31A3S0S2bSbaS2eG3RbRaA3A1S31A3S0S28G4A1S9eS3fReA1S2eG3RcRbA3A2S2aG4RaA2A3SbbS76RaS97A3S79Vsegs;S27G0S1aR12S19R11R10A2A4S27G0S1aR12S19S7eR11S3cRbA1A2R10A2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fe;Fdata;Fp;Fb;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 b p data e Hp Hi Hno Hfl Hdir Hc Hnd Hsl Hfs Hin.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@openat_file_intro_err (sys_input segs ms x8) m Hno Hfl Hdir e b p data Hc Hnd Hsl Hfs Hin).
  Qed.

  Lemma openat_file_only_ok : ltac2:(tb__ "0|4|
S7S37S15Q40M0A1M1S15Q8A1M2S29G2A1M3G3S77R5A1S0S76S16G0R5A2Z38A3S0S76S8eS16G0S6R8U2A2A2S95A2Z0A3S0G1S84S6R9U0A2A1S9bA3S0S42S3eS9RaA1S6RaU1A2A2S44S2eG2R7R6A3A1A3S0S2bS96S2eG2R8R7A3A1S31A3S0S2bSbaS2eG2R9R8A3A1S31A3S0S28G3A1S9eS3fRcA1S2eG2RaR9A3A2S2aG3R8A2A3S87S1bVsegs;ReRcA3RdA2F_;F_;F_;F_;F_;F_;F_;F_;Fdata;Fp;Fb;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 b p data [Hh Hl] Hno Hfl Hdir Hc Hnd Hsl Hfs.
    eapply only_ok_of_inv;
      [intros R; exact (@openat_file_inv (sys_input segs ms x8) m Hno Hfl Hdir R b p data Hc Hnd Hsl Hfs)| |].
    - intros [(e & _ & E) | (_ & E)]; unfold is_ret_ci in E; discriminate.
    - intros eff m' evs [(e & _ & E) | (_ & E)] _; unfold is_ret_ci in E; inversion E; subst; exact Hl.
  Qed.

  Lemma wstep_openat_absent_inv : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S15Q8A1M3S29G3A1M4S78S0S28G2A1S8R6A1S2aG2R4A2A3S77R6A1S0S76S16G1R6A2Z38A3S0S76S8eS16G1S6R9U2A2A2S95A2Z0A3S0G2S84S6RaU0A2A1S9bA3S0S42S3eS9RbA1S6RbU1A2A2S44S2eG3R8R7A3A1A3S0S2bS96S2eG3R9R8A3A1S31A3S0S2bSbaS2eG3RaR9A3A1S31A3S0S28G4A1S9eS3fRdA1S2eG3RbRaA3A2S2fG4A1A3S79Vsegs;S27G0S1aR10S19RfReA2A4RaA3S0S78RbS27G0S1aR11S19S7eR10S3cS59A1A2RfA2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fp;Fb;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 b p w' Hp Hi Hno Hfl Hdir Hc Hnd Hsl Hfs Hw.
    refine (@wstep_retci_inv0 _ _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. exact (@openat_absent_inv (sys_input segs ms x8) m Hno Hfl Hdir R b p Hc Hnd Hsl Hfs).
  Qed.

  Lemma wstep_openat_absent_intro : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S15Q8A1M3S29G3A1M4S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z38A3S0S76S8eS16G1S6R8U2A2A2S95A2Z0A3S0G2S84S6R9U0A2A1S9bA3S0S42S3eS9RaA1S6RaU1A2A2S44S2eG3R7R6A3A1A3S0S2bS96S2eG3R8R7A3A1S31A3S0S2bSbaS2eG3R9R8A3A1S31A3S0S28G4A1S9eS3fRcA1S2eG3RaR9A3A2S2fG4A1A3S79Vsegs;S27G0S1aRfS19ReRdA2A4S27G0S1aRfS19S7eReS3cS59A1A2RdA2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fp;Fb;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 b p Hp Hi Hno Hfl Hdir Hc Hnd Hsl Hfs.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@openat_absent_intro (sys_input segs ms x8) m Hno Hfl Hdir b p Hc Hnd Hsl Hfs).
  Qed.

  Lemma openat_absent_only_ok : ltac2:(tb__ "0|4|
S7S37S15Q40M0A1M1S15Q8A1M2S29G2A1M3S77R4A1S0S76S16G0R4A2Z38A3S0S76S8eS16G0S6R7U2A2A2S95A2Z0A3S0G1S84S6R8U0A2A1S9bA3S0S42S3eS9R9A1S6R9U1A2A2S44S2eG2R6R5A3A1A3S0S2bS96S2eG2R7R6A3A1S31A3S0S2bSbaS2eG2R8R7A3A1S31A3S0S28G3A1S9eS3fRbA1S2eG2R9R8A3A2S2fG3A1A3S87S1bVsegs;RdRbA3RcA2F_;F_;F_;F_;F_;F_;F_;F_;Fp;Fb;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 b p Hi Hno Hfl Hdir Hc Hnd Hsl Hfs.
    eapply only_ok_retci;
      [intros R; exact (@openat_absent_inv (sys_input segs ms x8) m Hno Hfl Hdir R b p Hc Hnd Hsl Hfs)| exact Hi].
  Qed.

  Definition openat_path_errno (c : cstr_result) : option Z := ltac2:(tb__ "0|3|
S42S28S76A1M0Lc;Vc;S29S15Q8A1M1A1M2G2G0Lp;R1S2aS76S59A2G1G2S2fS76A1Ll;Lb;X29x2Lp;S2aS76S67A2S2aS76S66A2X42x3").

  Lemma openat_patherr_spec_inv : ltac2:(tb__ "0|1|
S7S37S15Q40M0A1S76S99S39A1S0S76S16G0R3A2Z38A3S0S76S8eS16G0S6R6U2A2A2S95A2Z0A3S0S28S76A1S8aS3eS9R7A1S6R7U1A2A2A1S2aS76R4A2A3S86S1bVsegs;R8R6A3R7R4A3SacR5S3cR6A1Sb9S1bVsegs;R9R7A3A1R8S2cS36A1A5F_;F_;F_;F_;FR;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e R Hno Hfl He.
    destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc; cbn in He;
      inversion He; subst.
    - exact (@openat_empty_inv (sys_input segs ms x8) m Hno Hfl R Hc).
    - exact (@openat_toolong_inv (sys_input segs ms x8) m Hno Hfl R Hc).
    - exact (@openat_fault_inv (sys_input segs ms x8) m Hno Hfl R Hc).
  Qed.

  Lemma openat_patherr_spec_intro_ss : ltac2:(tb__ "0|4|
S7S37S15Q40M0A1M1S76S0S76S16G0R2A2Z38A3S0S76S8eS16G0S6R5U2A2A2S95A2Z0A3S0S28S76A1S8aS3eS9R6A1S6R6U1A2A2A1S2aS76R3A2A3S86S1bVsegs;R7R5A3M2R6S98S39S43S3cR4A1S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M3G3S2cS40A1Sb9G2A1A6R6S2cS36A1A4A3F_;F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e Hno Hfl He.
    destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc; cbn in He;
      inversion He; subst.
    - exact (@openat_empty_intro (sys_input segs ms x8) m Hno Hfl Hc).
    - exact (@openat_toolong_intro (sys_input segs ms x8) m Hno Hfl Hc).
    - exact (@openat_fault_intro (sys_input segs ms x8) m Hno Hfl Hc).
  Qed.

  Lemma openat_patherr_spec_intro : ltac2:(tb__ "0|4|
S7S37S15Q40M0A1M1S76S0S76S16G0R2A2Z38A3S0S76S8eS16G0S6R5U2A2A2S95A2Z0A3S0S28S76A1S8aS3eS9R6A1S6R6U1A2A2A1S2aS76R3A2A3Sc8S1bVsegs;R7R5A3M2R6S98S39S43S3cR4A1S2cS2dG1S29S15Q8A1A1A2A1S2cS2dG1G1A2A1M3G3S2cS40A1Sb9G2A1A6R6S2cS36A1A4A3F_;F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros. split; [eapply openat_patherr_spec_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma wstep_openat_patherr_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S76S78S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z38A3S0S76S8eS16G1S6R8U2A2A2S95A2Z0A3S0S28S76A1S8aS3eS9R9A1S6R9U1A2A2A1S2aS76R6A2A3S79Vsegs;S27G0S1aRbS19RaR9A2A4R6A3S0S78R7S27G0S1aRcS19S7eRbS3cR8A1A2RaA2A4A3F_;F_;F_;F_;F_;F_;Fw';Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e w' Hp Hi Hno Hfl He Hw.
    refine (@wstep_retci_inv0 _ _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. exact (@openat_patherr_spec_inv ms m x8 e R Hno Hfl He).
  Qed.

  Lemma wstep_openat_patherr_intro : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S76S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z38A3S0S76S8eS16G1S6R7U2A2A2S95A2Z0A3S0S28S76A1S8aS3eS9R8A1S6R8U1A2A2A1S2aS76R5A2A3S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7eR9S3cR6A1A2R8A2A4A3F_;F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hi Hno Hfl He.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@openat_patherr_spec_intro ms m x8 e Hno Hfl He).
  Qed.

  Lemma openat_patherr_only_ok : ltac2:(tb__ "0|1|
S7S37S15Q40M0A1S76S77R3A1S0S76S16G0R3A2Z38A3S0S76S8eS16G0S6R6U2A2A2S95A2Z0A3S0S28S76A1S8aS3eS9R7A1S6R7U1A2A2A1S2aS76R4A2A3S87S1bVsegs;R8R6A3R7A2F_;F_;F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e Hi Hno Hfl He.
    eapply only_ok_retci; [intros R; exact (@openat_patherr_spec_inv ms m x8 e R Hno Hfl He)| exact Hi].
  Qed.

  Lemma wstep_openat_dot_inv : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z38A3S0S76S8eS16G1S6R7U2A2A2S95A2Z0A3S0G2S84S6R8U0A2A1S9bA3S0S42S3eS9R9A1S6R9U1A2A2S44S9dA1A3S79Vsegs;S27G0S1aRbS19RaR9A2A4R7A3S3S4S76S76S1SbbS76R1S97A3S0S78R9S27G0S1aRdS19S7eRcS3cR1A1A2RbA2A4A3A2Le;A2S1S0S28S38A1S3dS3bRaA1M3S48G3A1M4A2S2fS38A1A3S0S78R8S27G0S1aRcS19S7eRbG4A2SafRaA1A2A4A3A2A2F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Hfl Hdir Hc Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@openat_dot_inv (sys_input segs ms x8) m Hno Hfl Hdir _ Hc) in Hspec.
    destruct Hspec as [(e & Hin & E) | (Hfree & E)]; unfold is_ret_ci in E; inversion E; subst.
    - left. exists e. split; [exact Hin|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. split; [exact Hfree|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  Lemma wstep_openat_dot_intro_ok : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2Z38A3S0S76S8eS16G1S6R6U2A2A2S95A2Z0A3S0G2S84S6R7U0A2A1S9bA3S0S42S3eS9R8A1S6R8U1A2A2S44S9dA1A3S0S28S38A1S3dS3bR8A1M3S48G3A1A2S2fS38A1A3S79Vsegs;S27G0S1aRbS19RaR9A2A4S27G0S1aRbS19S7eRaS48S3bR9A1A1A2SafR9A1A2A4A3F_;F_;F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hfl Hdir Hc Hfree.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ (with_fds_idle _ Hi)).
    exact (@openat_dot_intro_ok (sys_input segs ms x8) m Hno Hfl Hdir Hc Hfree).
  Qed.

  Lemma wstep_openat_dot_intro_err : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S76S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z38A3S0S76S8eS16G1S6R7U2A2A2S95A2Z0A3S0G2S84S6R8U0A2A1S9bA3S0S42S3eS9R9A1S6R9U1A2A2S44S9dA1A3SbbS76R7S97A3S79Vsegs;S27G0S1aRcS19RbRaA2A4S27G0S1aRcS19S7eRbS3cR8A1A2RaA2A4A3F_;F_;F_;F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hi Hno Hfl Hdir Hc Hin.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@openat_dot_intro_err (sys_input segs ms x8) m Hno Hfl Hdir e Hc Hin).
  Qed.

  Lemma openat_dot_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1M1S77R2A1S0S76S16G0R2A2Z38A3S0S76S8eS16G0S6R5U2A2A2S95A2Z0A3S0G1S84S6R6U0A2A1S9bA3S0S42S3eS9R7A1S6R7U1A2A2S44S9dA1A3S87S1bVsegs;R8R6A3R7A2F_;F_;F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 [Hh Hl] Hno Hfl Hdir Hc.
    eapply only_ok_of_inv;
      [intros R; exact (@openat_dot_inv (sys_input segs ms x8) m Hno Hfl Hdir R Hc)| |].
    - intros [(e & _ & E) | (_ & E)]; unfold is_ret_ci in E; discriminate.
    - intros eff m' evs [(e & _ & E) | (_ & E)] _; unfold is_ret_ci in E; inversion E; subst; exact Hl.
  Qed.

  Lemma wstep_openat_dirref_inv : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S29S15Q8A1A1S78S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z38A3S0S76S8eS16G1S6R8U2A2A2S95A2Z0A3S0G2S84S6R9U0A2A1S9bA3S0S42S3eS9RaA1S6RaU1A2A2S44R7A1A3S0S2bS96R8A1S30A3S79Vsegs;S27G0S1aRdS19RcRbA2A4R8A3S3S4S76S76S1SbbS76R1S97A3S0S78RaS27G0S1aRfS19S7eReS3cR1A1A2RdA2A4A3A2Le;A2S1S0S28S38A1S3dS3bRcA1M3S48G3A1M4A2S2fS38A1A3S0S78R9S27G0S1aReS19S7eRdG4A2SafRcA1A2A4A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fq;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 q w' Hp [Hh Hl] Hno Hfl Hdir Hc Hd Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@openat_dirref_inv (sys_input segs ms x8) m Hno Hfl Hdir _ q Hc Hd) in Hspec.
    destruct Hspec as [(e & Hin & E) | (Hfree & E)]; unfold is_ret_ci in E; inversion E; subst.
    - left. exists e. split; [exact Hin|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. split; [exact Hfree|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  Lemma wstep_openat_dirref_intro_ok : ltac2:(tb__ "0|4|
S29S36A1M0S7S37S15Q40M1A1M2S29S15Q8A1A1S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Z38A3S0S76S8eS16G1S6R7U2A2A2S95A2Z0A3S0G2S84S6R8U0A2A1S9bA3S0S42S3eS9R9A1S6R9U1A2A2S44R6A1A3S0S2bS96R7A1S30A3S0S28S38A1S3dS3bRaA1M3S48G3A1A2S2fS38A1A3S79Vsegs;S27G0S1aRdS19RcRbA2A4S27G0S1aRdS19S7eRcS48S3bRbA1A1A2SafRbA1A2A4A3F_;F_;F_;F_;F_;F_;F_;F_;Fq;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 q Hp Hi Hno Hfl Hdir Hc Hd Hfree.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ (with_fds_idle _ Hi)).
    exact (@openat_dirref_intro_ok (sys_input segs ms x8) m Hno Hfl Hdir q Hc Hd Hfree).
  Qed.

  Lemma wstep_openat_dirref_intro_err : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S29S15Q8A1A1S76S0S28G2A1S8R5A1S2aG2R3A2A3S77R5A1S0S76S16G1R5A2Z38A3S0S76S8eS16G1S6R8U2A2A2S95A2Z0A3S0G2S84S6R9U0A2A1S9bA3S0S42S3eS9RaA1S6RaU1A2A2S44R7A1A3S0S2bS96R8A1S30A3SbbS76R8S97A3S79Vsegs;S27G0S1aReS19RdRcA2A4S27G0S1aReS19S7eRdS3cR9A1A2RcA2A4A3F_;F_;F_;F_;F_;F_;F_;F_;Fe;Fq;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 q e Hp Hi Hno Hfl Hdir Hc Hd Hin.
    refine (@wstep_retci_intro0 tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@openat_dirref_intro_err (sys_input segs ms x8) m Hno Hfl Hdir e q Hc Hd Hin).
  Qed.

  Lemma openat_dirref_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1M1S29S15Q8A1A1S77R3A1S0S76S16G0R3A2Z38A3S0S76S8eS16G0S6R6U2A2A2S95A2Z0A3S0G1S84S6R7U0A2A1S9bA3S0S42S3eS9R8A1S6R8U1A2A2S44R5A1A3S0S2bS96R6A1S30A3S87S1bVsegs;RaR8A3R9A2F_;F_;F_;F_;F_;F_;Fq;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 q [Hh Hl] Hno Hfl Hdir Hc Hd.
    eapply only_ok_of_inv;
      [intros R; exact (@openat_dirref_inv (sys_input segs ms x8) m Hno Hfl Hdir R q Hc Hd)| |].
    - intros [(e & _ & E) | (_ & E)]; unfold is_ret_ci in E; discriminate.
    - intros eff m' evs [(e & _ & E) | (_ & E)] _; unfold is_ret_ci in E; inversion E; subst; exact Hl.
  Qed.

  Lemma wstep_mmap_inv : ltac2:(tb__ "0|6|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2ZdeA3S2S0G2S6R7U1M3A2S17G1Z0A2A3A1S0S2bSa3S6R8U2A2S6R8U3M4A2S6R8U5A2A3S30A3S0S2bSa2S6R9G4A2A1S31A3S79Vsegs;S27G0S1aRbS19RaR9A2A4R7A3S3S0S78R8S27G0S1aRcS19S7eRbS3cS4bA1A2RaA2A4A3S4G2G2S1Sb5S6RcU0A2S6RcG4A2RbS6RcG3A2M5R1A5S0S78R9S27G0S1aRdS19S7fRcR1S81SaRcA1R1SaeG5A1A3A3S54Sb7S41RbA1G5R1A3RbA2A2A4A3A2La;A2A2F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Hlen Hsh Hnr Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@mmap_rw_inv (sys_input segs ms x8) m Hno Hlen Hsh) in Hspec.
    destruct Hspec as [E | (a & Hpl & E)]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. exists a. split; [exact Hpl|].
      unfold mmap_rw_model in Hcases. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hcases.
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr) in Hcases.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  Lemma wstep_mmap_intro_fail : ltac2:(tb__ "0|5|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2ZdeA3S2S0G2S6R6U1M3A2S17G1Z0A2A3A1S0S2bSa3S6R7U2A2S6R7U3M4A2S6R7U5A2A3S30A3S0S2bSa9S6R8G4A2R7SabS6R8G3A2A1A3S30A3S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7eR9S3cS4bA1A2R8A2A4A3F_;F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hlen Hsh Hrf.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@mmap_rw_intro_fail (sys_input segs ms x8) m Hno Hlen Hsh Hrf).
  Qed.

  Lemma wstep_mmap_intro_ok : ltac2:(tb__ "0|6|
S29S36A1M0S7S37S15Q40M1A1M2G2S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2ZdeA3S2S0G2S6R7U1M3A2S17G1Z0A2A3A1S0S2bSa3S6R8U2A2S6R8U3M4A2S6R8U5A2A3S30A3S0S2bSa2S6R9G4A2A1S31A3Sb5S6RaU0A2S6RaG4A2R9S6RaG3A2R7A5S79Vsegs;S27G0S1aRcS19RbRaA2A4S27G0S1aRcS19S7fRbR8S81SaRbA1R8SaeS6RbG3A2M5A1A3A3S54Sb7S41RaA1G5R8A3RaA2A2A4A3F_;F_;F_;F_;F_;F_;F_;Fa;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 a Hp Hi Hno Hlen Hsh Hnr Hpl.
    pose proof (@mmap_rw_intro_ok (sys_input segs ms x8) m Hno Hlen Hsh a Hpl) as Hs.
    unfold mmap_rw_model in Hs. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hs.
    rewrite (with_mmap_backing_plain _ _ _ _ Hnr) in Hs.
    refine (@wstep_pending_run0 tr _ _ _ _ _ Hp (model_idle_halted Hi) Hs _).
    destruct Hi as [H1 H2]; split; assumption.
  Qed.

  Lemma mmap_only_ok : ltac2:(tb__ "0|3|
S7S37S15Q40M0A1M1S77R2A1S0S76S16G0R2A2ZdeA3S2S0G1S6R5U1A2S17G0Z0A2A3A1S0S2bSa3S6R6U2A2S6R6U3M2A2S6R6U5A2A3S30A3S0S2bSa2S6R7G2A2A1S31A3S87S1bVsegs;R8R6A3R7A2F_;F_;F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 [Hh Hl] Hno Hlen Hsh Hnr.
    eapply only_ok_of_inv; [intros R; exact (@mmap_rw_inv (sys_input segs ms x8) m Hno Hlen Hsh R)| |].
    - intros [E | (a & _ & E)]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | (a & _ & E)] _; unfold is_ret in E; inversion E; subst; [exact Hl|].
      unfold mmap_rw_model. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact Hl.
  Qed.

  Lemma wstep_mmap_none_inv : ltac2:(tb__ "0|8|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2ZdeA3S2S0G2S6R7U1M3A2S17G1Z0A2A3A1S0S2bSa4S6R8U2M4A2S6R8U3M5A2S6R8U5M6A2A3S30A3S0S2bSa3S6R9G4A2S6R9G5A2S6R9G6A2A3S31A3S0S2bSa2S6RaG5A2A1S31A3S79Vsegs;S27G0S1aRcS19RbRaA2A4R8A3S3S0S78R9S27G0S1aRdS19S7eRcS3cS4bA1A2RbA2A4A3S4G2G2S1Sb6S6RdU0A2RcS6RdG3A2M7R1A4S0S78RaS27G0S1aReS19S7fRdR1S80SaRdA1R1SaeG7A1A3A3S54Sb4S41RcA1G7R1A3RcA2A2A4A3A2La;A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Hlen Hsh Hnrw Hnr Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@mmap_none_inv (sys_input segs ms x8) m Hno Hlen Hsh Hnrw) in Hspec.
    destruct Hspec as [E | (a & Hpl & E)]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
    - right. exists a. split; [exact Hpl|].
      unfold mmap_none_model in Hcases. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hcases.
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr) in Hcases.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  Lemma wstep_mmap_none_intro_fail : ltac2:(tb__ "0|7|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2ZdeA3S2S0G2S6R6U1M3A2S17G1Z0A2A3A1S0S2bSa4S6R7U2M4A2S6R7U3M5A2S6R7U5M6A2A3S30A3S0S2bSa3S6R8G4A2S6R8G5A2S6R8G6A2A3S31A3S0S2bSaaR8SabS6R9G3A2A1A2S30A3S79Vsegs;S27G0S1aRbS19RaR9A2A4S27G0S1aRbS19S7eRaS3cS4bA1A2R9A2A4A3F_;F_;F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hlen Hsh Hnrw Hrf.
    refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@mmap_none_intro_fail (sys_input segs ms x8) m Hno Hlen Hsh Hnrw Hrf).
  Qed.

  Lemma wstep_mmap_none_intro_ok : ltac2:(tb__ "0|8|
S29S36A1M0S7S37S15Q40M1A1M2G2S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2ZdeA3S2S0G2S6R7U1M3A2S17G1Z0A2A3A1S0S2bSa4S6R8U2M4A2S6R8U3M5A2S6R8U5M6A2A3S30A3S0S2bSa3S6R9G4A2S6R9G5A2S6R9G6A2A3S31A3S0S2bSa2S6RaG5A2A1S31A3Sb6S6RbU0A2RaS6RbG3A2R8A4S79Vsegs;S27G0S1aRdS19RcRbA2A4S27G0S1aRdS19S7fRcR9S80SaRcA1R9SaeS6RcG3A2M7A1A3A3S54Sb4S41RbA1G7R9A3RbA2A2A4A3F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 a Hp Hi Hno Hlen Hsh Hnrw Hnr Hpl.
    pose proof (@mmap_none_intro_ok (sys_input segs ms x8) m Hno Hlen Hsh Hnrw a Hpl) as Hs.
    unfold mmap_none_model in Hs. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hs.
    rewrite (with_mmap_backing_plain _ _ _ _ Hnr) in Hs.
    refine (@wstep_pending_run0 tr _ _ _ _ _ Hp (model_idle_halted Hi) Hs _).
    destruct Hi as [H1 H2]; split; assumption.
  Qed.

  Lemma mmap_none_only_ok : ltac2:(tb__ "0|5|
S7S37S15Q40M0A1M1S77R2A1S0S76S16G0R2A2ZdeA3S2S0G1S6R5U1A2S17G0Z0A2A3A1S0S2bSa4S6R6U2M2A2S6R6U3M3A2S6R6U5M4A2A3S30A3S0S2bSa3S6R7G2A2S6R7G3A2S6R7G4A2A3S31A3S0S2bSa2S6R8G3A2A1S31A3S87S1bVsegs;R9R7A3R8A2F_;F_;F_;F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 [Hh Hl] Hno Hlen Hsh Hnrw Hnr.
    eapply only_ok_of_inv;
      [intros R; exact (@mmap_none_inv (sys_input segs ms x8) m Hno Hlen Hsh Hnrw R)| |].
    - intros [E | (a & _ & E)]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | (a & _ & E)] _; unfold is_ret in E; inversion E; subst; [exact Hl|].
      unfold mmap_none_model. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact Hl.
  Qed.

  Section MmapFixedW.
    Variables (ms : machine_state) (m : Model) (x8 : word).
    Let addr := ms_gpr ms 0.
    Let len := ms_gpr ms 1.
    Let flags := ms_gpr ms 3.
    Let h := m_vmmaps m.
    Let n := mmap_n len.
    Hypothesis Hno : bv_unsigned x8 = 222%Z.
    Hypothesis Hlen : len <> Z_to_bv 64 0.
    Hypothesis Hsh : ltac2:(tb__ "0|0|
S0S2bSa8S6Vms;U2A2S6Vms;U3A2S6Vms;U5A2A3S30A3").
    Hypothesis Hnn : ltac2:(tb__ "0|0|
S0S2bSa4S6Vms;U2A2S6Vms;U3A2S6Vms;U5A2A3S31A3").
    Hypothesis Hnrw : ltac2:(tb__ "0|0|
S0S2bSa3S6Vms;U2A2S6Vms;U3A2S6Vms;U5A2A3S31A3").

    Hypothesis Hceil : ltac2:(tb__ "0|0|
S8dS90S16Q40Vaddr;A2SabVlen;A1A2S6aS41Vm;A1A1A2").
    Hypothesis Halign : ltac2:(tb__ "0|0|
S0S76S91S16Q40Vaddr;A2S60A2Z0A3").
    Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
    Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S2bS56S75Vh;A1Vaddr;Vn;A3S30A3").
    Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3").

    Lemma mmap_fixed_ok_model_lazy : ltac2:(tb__ "0|4|
S0S2bSa2Vflags;A1S31A3S0S29S2dS15Q40A1M0G0A2M1A1M2S4dVm;A1S2cG1A1M3A3S0G2S4dSb0Vflags;Vm;Vaddr;Vn;A4A1G3A3F_;F_;").
    Proof using len.
      intros Hnr Hl. unfold mmap_fixed_ok_model, with_mmap_replacement.
      rewrite (with_mmap_backing_plain _ _ _ _ Hnr). apply m_vm_lazy_vm_forget_range. exact Hl.
    Qed.

    Lemma mmap_fixed_dead_model_lazy : ltac2:(tb__ "0|4|
S0S29S2dS15Q40A1M0G0A2M1A1M2S4dVm;A1S2cG1A1M3A3S0G2S4dSb3Vm;Vaddr;Vn;A3A1G3A3F_;").
    Proof using len.
      intros Hl. unfold mmap_fixed_dead_model, with_mmap_destroyed.
      apply m_vm_lazy_vm_forget_range. exact Hl.
    Qed.

    Lemma wstep_mmap_fixed_inv : ltac2:(tb__ "0|4|
S29S36A1M0S78S0S28S15Q40A1M1A1S8Vms;A1S2aG1Vx8;A2A3S77Vm;A1S0S2bSa2Vflags;A1S31A3S79Vsegs;S27G0S1aR5S19Vms;Vm;A2A4R4A3S3S0S78R5S27G0S1aR6S19S7eVms;S3cS4bA1M2A2Vm;A2A4A3S3S0S78R5S27G0S1aR6S19S7fVms;Vaddr;S80SaVms;A1Vaddr;Vn;A3M3A3Sb0Vflags;Vm;Vaddr;Vn;A4A2A4A3S0S78R5S27G0S1aR6S19S7fVms;G2G3A3Sb3Vm;Vaddr;Vn;A3A2A4A3A2A2F_;F_;F_;F_;Fw';Ftr;").
    Proof using Halign Hceil Hcont Hfree Hlen Hnn Hno Hnrw Hpos Hsh.
      intros tr w' Hp [Hh Hl] Hnr Hw.
      destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
      apply (@mmap_fixed_inv (sys_input segs ms x8) m Hno Hlen Hsh Hnn Hnrw Hceil Halign Hpos Hfree Hcont)
        in Hspec.
      destruct Hspec as [E | [E | E]]; unfold is_ret in E; inversion E; subst.
      - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
        mat_id Hm Hl. now rewrite app_nil_r.
      - right; left.
        destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
        + mat_id Hm (mmap_fixed_ok_model_lazy Hnr Hl). now rewrite app_nil_r.
        + exfalso. msimp Hcd. congruence.
      - right; right.
        destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
        + mat_id Hm (mmap_fixed_dead_model_lazy Hl). now rewrite app_nil_r.
        + exfalso. msimp Hcd. congruence.
    Qed.

    Lemma wstep_mmap_fixed_intro_ok : ltac2:(tb__ "0|2|
S29S36A1M0S0S28S15Q40A1M1A1S8Vms;A1S2aG1Vx8;A2A3S77Vm;A1S0S2bSa2Vflags;A1S31A3S79Vsegs;S27G0S1aR4S19Vms;Vm;A2A4S27G0S1aR4S19S7fVms;Vaddr;S80SaVms;A1Vaddr;Vn;A3A3Sb0Vflags;Vm;Vaddr;Vn;A4A2A4A3F_;F_;F_;Ftr;").
    Proof using Halign Hceil Hcont Hfree Hlen Hnn Hno Hnrw Hpos Hsh.
      intros tr Hp [Hh Hl] Hnr.
      pose proof (@mmap_fixed_intro_ok (sys_input segs ms x8) m Hno Hlen Hsh Hnn Hnrw
                    Hceil Halign Hpos Hfree Hcont) as Hs.
      refine (@wstep_pending_run0 tr _ _ _ _ _ Hp Hh Hs _). split.
      - unfold mmap_fixed_ok_model, with_mmap_replacement.
        rewrite (with_mmap_backing_plain _ _ _ _ Hnr), m_halted_vm_forget_range. exact Hh.
      - exact (mmap_fixed_ok_model_lazy Hnr Hl).
    Qed.

    Lemma mmap_fixed_only_ok : ltac2:(tb__ "0|0|
S77Vm;A1S0S2bSa2Vflags;A1S31A3S87S1bVsegs;Vms;Vx8;A3Vm;A2F_;F_;").
    Proof using Halign Hceil Hcont Hfree Hlen Hnn Hno Hnrw Hpos Hsh.
      intros [Hh Hl] Hnr.
      eapply only_ok_of_inv;
        [intros R; exact (@mmap_fixed_inv (sys_input segs ms x8) m Hno Hlen Hsh Hnn Hnrw
                            Hceil Halign Hpos Hfree Hcont R)| |].
      - intros [E | [E | E]]; unfold is_ret in E; discriminate.
      - intros eff m' evs [E | [E | E]] _; unfold is_ret in E; inversion E; subst;
          [exact Hl | exact (mmap_fixed_ok_model_lazy Hnr Hl) | exact (mmap_fixed_dead_model_lazy Hl)].
    Qed.
  End MmapFixedW.

  Section MunmapW.
    Variables (ms : machine_state) (m : Model) (x8 : word).
    Let addr := ms_gpr ms 0.
    Let len := ms_gpr ms 1.
    Let h := m_vmmaps m.
    Let n := mmap_n len.
    Hypothesis Hno : bv_unsigned x8 = 215%Z.
    Hypothesis Halign : ltac2:(tb__ "0|0|
S0S76S91S16Q40Vaddr;A2S60A2Z0A3").
    Hypothesis Hlen : len <> Z_to_bv 64 0.

    Hypothesis Htask : ltac2:(tb__ "0|0|
S8dS90S16Q40Vaddr;A2SabVlen;A1A2S4aA2").

    Lemma munmap_model_idle : ltac2:(tb__ "0|0|
S77Vm;A1S77Sb1Vm;Vaddr;Vn;A3A1F_;").
    Proof using len.
      intros [Hh Hl]. unfold munmap_model, with_mmap_destroyed. split.
      - rewrite m_halted_vm_forget_range. exact Hh.
      - apply m_vm_lazy_vm_forget_range. exact Hl.
    Qed.

    Lemma wstep_munmap_exact_inv : ltac2:(tb__ "0|3|
S29S36A1M0S78S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS53S46Vh;A1Vaddr;Vn;A3S30A3S79Vsegs;S27G0S1aR5S19Vms;Vm;A2A4R4A3S0S78R5S27G0S1aR6S19S7fVms;S17G1Z0A2S80SaVms;A1Vaddr;Vn;A3A3Sb1Vm;Vaddr;Vn;A3A2A4A3F_;F_;F_;F_;Fw';Ftr;").
    Proof using Halign Hlen Hno Htask.
      intros tr w' Hp Hi Hhas Hw. pose proof Hi as [Hh Hl].
      destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
      apply (@munmap_exact_inv (sys_input segs ms x8) m Hno Halign Hlen Htask _ Hhas) in Hspec.
      inversion Hspec; subst.
      destruct (munmap_model_idle Hi) as [Hh1 Hl1].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl1. now rewrite app_nil_r.
    Qed.

    Lemma wstep_munmap_exact_intro : ltac2:(tb__ "0|3|
S29S36A1M0S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS53S46Vh;A1Vaddr;Vn;A3S30A3S79Vsegs;S27G0S1aR4S19Vms;Vm;A2A4S27G0S1aR4S19S7fVms;S17G1Z0A2S80SaVms;A1Vaddr;Vn;A3A3Sb1Vm;Vaddr;Vn;A3A2A4A3F_;F_;F_;Ftr;").
    Proof using Halign Hlen Hno Htask.
      intros tr Hp Hi Hhas.
      pose proof (@munmap_exact_intro (sys_input segs ms x8) m Hno Halign Hlen Htask Hhas) as Hs.
      exact (@wstep_pending_run0 tr _ _ _ _ _ Hp (model_idle_halted Hi) Hs (munmap_model_idle Hi)).
    Qed.

    Lemma munmap_exact_only_ok : ltac2:(tb__ "0|0|
S77Vm;A1S0S2bS53S46Vh;A1Vaddr;Vn;A3S30A3S87S1bVsegs;Vms;Vx8;A3Vm;A2F_;F_;").
    Proof using Halign Hlen Hno Htask.
      intros Hi Hhas. eapply only_ok_of_inv;
        [intros R; exact (@munmap_exact_inv (sys_input segs ms x8) m Hno Halign Hlen Htask R Hhas)| |].
      - discriminate.
      - intros eff m' evs E _. inversion E; subst. exact (model_idle_lazy (munmap_model_idle Hi)).
    Qed.

    Lemma wstep_munmap_free_inv : ltac2:(tb__ "0|3|
S29S36A1M0S78S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS53S46Vh;A1Vaddr;Vn;A3S31A3S0S2bSa5Vh;Vaddr;SabVlen;A1A3S30A3S79Vsegs;S27G0S1aR6S19Vms;Vm;A2A4R5A3S0S78R6S27G0S1aR7S19S7eVms;S17G1Z0A2A2Vm;A2A4A3F_;F_;F_;F_;F_;Fw';Ftr;").
    Proof using Halign Hlen Hno Htask.
      intros tr w' Hp Hi Hhas Hrf Hw. refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
      intros R. exact (@munmap_free_inv (sys_input segs ms x8) m Hno Halign Hlen Htask R Hhas Hrf).
    Qed.

    Lemma wstep_munmap_free_intro : ltac2:(tb__ "0|3|
S29S36A1M0S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS53S46Vh;A1Vaddr;Vn;A3S31A3S0S2bSa5Vh;Vaddr;SabVlen;A1A3S30A3S79Vsegs;S27G0S1aR5S19Vms;Vm;A2A4S27G0S1aR5S19S7eVms;S17G1Z0A2A2Vm;A2A4A3F_;F_;F_;F_;Ftr;").
    Proof using Halign Hlen Hno Htask.
      intros tr Hp Hi Hhas Hrf. refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
      exact (@munmap_free_intro (sys_input segs ms x8) m Hno Halign Hlen Htask Hhas Hrf).
    Qed.

    Lemma munmap_free_only_ok : ltac2:(tb__ "0|0|
S77Vm;A1S0S2bS53S46Vh;A1Vaddr;Vn;A3S31A3S0S2bSa5Vh;Vaddr;SabVlen;A1A3S30A3S87S1bVsegs;Vms;Vx8;A3Vm;A2F_;F_;F_;").
    Proof using Halign Hlen Hno Htask.
      intros Hi Hhas Hrf. eapply only_ok_ret;
        [intros R; exact (@munmap_free_inv (sys_input segs ms x8) m Hno Halign Hlen Htask R Hhas Hrf)| exact Hi].
    Qed.
  End MunmapW.

  Section MprotectW.
    Variables (ms : machine_state) (m : Model) (x8 : word).
    Let addr := ms_gpr ms 0.
    Let len := ms_gpr ms 1.
    Let h := m_vmmaps m.
    Let n := mmap_n len.
    Hypothesis Hno : bv_unsigned x8 = 226%Z.
    Hypothesis Hprot : bv_unsigned (ms_gpr ms 2) = 3%Z.
    Hypothesis Halign : ltac2:(tb__ "0|0|
S0S76S91S16Q40Vaddr;A2S60A2Z0A3").
    Hypothesis Hlen : len <> Z_to_bv 64 0.
    Hypothesis Hwrap : ltac2:(tb__ "0|0|
S8fS90S16Q40Vaddr;A2SabVlen;A1A2S74A2").

    Lemma mprotect_model_next_idle : ltac2:(tb__ "0|0|
S77Vm;A1S77Sc4Vm;Vaddr;Vn;A3A1F_;").
    Proof using len. intros [Hh Hl]. split; assumption. Qed.

    Lemma wstep_mprotect_expose_inv : ltac2:(tb__ "0|3|
S29S36A1M0S78S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS45S4fVh;A1Vaddr;Vn;A3S30A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S79Vsegs;S27G0S1aR6S19Vms;Vm;A2A4R5A3S3S0S78R6S27G0S1aR7S19S7eVms;S3cS4bA1A2Vm;A2A4A3S1S0S2bSc3Vm;Vaddr;Vn;A3S30A3S0S78R6S27G0S1aR7S19S7fVms;S17G1Z0A2S81SaVms;A1Vaddr;Vn;A3A3Sc4Vm;Vaddr;Vn;A3A2A4A3A2A2F_;F_;F_;F_;F_;Fw';Ftr;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros tr w' Hp Hi Hna Hmp Hw. pose proof Hi as [Hh Hl].
      destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
      apply (@mprotect_expose_inv (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp) in Hspec.
      destruct Hspec as [E | (Hb & E)]; unfold is_ret in E; inversion E; subst.
      - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
        mat_id Hm Hl. now rewrite app_nil_r.
      - right. split; [exact Hb|].
        destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
        mat_id Hm (model_idle_lazy (mprotect_model_next_idle Hi)). now rewrite app_nil_r.
    Qed.

    Lemma wstep_mprotect_expose_intro_ok : ltac2:(tb__ "0|3|
S29S36A1M0S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS45S4fVh;A1Vaddr;Vn;A3S30A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S0S2bSc3Vm;Vaddr;Vn;A3S30A3S79Vsegs;S27G0S1aR6S19Vms;Vm;A2A4S27G0S1aR6S19S7fVms;S17G1Z0A2S81SaVms;A1Vaddr;Vn;A3A3Sc4Vm;Vaddr;Vn;A3A2A4A3F_;F_;F_;F_;F_;Ftr;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros tr Hp Hi Hna Hmp Hb.
      pose proof (@mprotect_expose_intro_ok (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hb) as Hs.
      exact (@wstep_pending_run0 tr _ _ _ _ _ Hp (model_idle_halted Hi) Hs (mprotect_model_next_idle Hi)).
    Qed.

    Lemma wstep_mprotect_expose_intro_fail : ltac2:(tb__ "0|2|
S29S36A1M0S0S28S15Q40A1M1A1S8Vms;A1S2aG1Vx8;A2A3S77Vm;A1S0S2bS45S4fVh;A1Vaddr;Vn;A3S30A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S0S2bSc3Vm;Vaddr;Vn;A3S31A3S79Vsegs;S27G0S1aR6S19Vms;Vm;A2A4S27G0S1aR6S19S7eVms;S3cS4bA1A2Vm;A2A4A3F_;F_;F_;F_;F_;Ftr;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros tr Hp Hi Hna Hmp Hb. refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
      exact (@mprotect_expose_intro_fail (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hb).
    Qed.

    Lemma mprotect_expose_only_ok : ltac2:(tb__ "0|0|
S77Vm;A1S0S2bS45S4fVh;A1Vaddr;Vn;A3S30A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S87S1bVsegs;Vms;Vx8;A3Vm;A2F_;F_;F_;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros Hi Hna Hmp. pose proof Hi as [Hh Hl]. eapply only_ok_of_inv;
        [intros R; exact (@mprotect_expose_inv (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap
                            Hna Hmp R)| |].
      - intros [E | (_ & E)]; unfold is_ret in E; discriminate.
      - intros eff m' evs [E | (_ & E)] _; unfold is_ret in E; inversion E; subst;
          [exact Hl | exact (model_idle_lazy (mprotect_model_next_idle Hi))].
    Qed.

    Lemma wstep_mprotect_noop_inv : ltac2:(tb__ "0|4|
S29S36A1M0S78S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS45S4fVh;A1M3Vaddr;Vn;A3S31A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S0S2bS56G3Vaddr;Vn;A3S30A3S79Vsegs;S27G0S1aR7S19Vms;Vm;A2A4R6A3S0S78R7S27G0S1aR8S19S7eVms;S17G1Z0A2A2Vm;A2A4A3F_;F_;F_;F_;F_;F_;Fw';Ftr;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros tr w' Hp Hi Hna Hmp Hrf Hw. refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
      intros R. exact (@mprotect_noop_inv (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap
                         Hna Hmp Hrf R).
    Qed.

    Lemma wstep_mprotect_noop_intro : ltac2:(tb__ "0|4|
S29S36A1M0S0S28S15Q40M1A1M2A1S8Vms;A1S2aG2Vx8;A2A3S77Vm;A1S0S2bS45S4fVh;A1M3Vaddr;Vn;A3S31A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S0S2bS56G3Vaddr;Vn;A3S30A3S79Vsegs;S27G0S1aR6S19Vms;Vm;A2A4S27G0S1aR6S19S7eVms;S17G1Z0A2A2Vm;A2A4A3F_;F_;F_;F_;F_;Ftr;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros tr Hp Hi Hna Hmp Hrf. refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
      exact (@mprotect_noop_intro (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hrf).
    Qed.

    Lemma mprotect_noop_only_ok : ltac2:(tb__ "0|1|
S77Vm;A1S0S2bS45S4fVh;A1M0Vaddr;Vn;A3S31A3S0S2bS45S46Vh;A1Vaddr;Vn;A3S30A3S0S2bS56G0Vaddr;Vn;A3S30A3S87S1bVsegs;Vms;Vx8;A3Vm;A2F_;F_;F_;F_;").
    Proof using Halign Hlen Hno Hprot Hwrap.
      intros Hi Hna Hmp Hrf. eapply only_ok_ret;
        [intros R; exact (@mprotect_noop_inv (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap
                            Hna Hmp Hrf R)| exact Hi].
    Qed.
  End MprotectW.

  Lemma wstep_brk_query_inv : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Zd6A3S0G2S6R7U0A2S17G1Z0A2A3S79Vsegs;S27G0S1aR9S19R8R7A2A4R5A3S0S78R6S27G0S1aRaS19S7eR9S47S41R8A1A1A2R8A2A4A3F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp Hi Hno Hq Hw. refine (@wstep_ret_inv0 _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. exact (@brk_query_inv (sys_input segs ms x8) m R Hno Hq).
  Qed.

  Lemma wstep_brk_query_intro : ltac2:(tb__ "0|3|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2Zd6A3S0G2S6R6U0A2S17G1Z0A2A3S79Vsegs;S27G0S1aR8S19R7R6A2A4S27G0S1aR8S19S7eR7S47S41R6A1A1A2R6A2A4A3F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hq. refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@brk_query_intro (sys_input segs ms x8) m Hno Hq).
  Qed.

  Lemma brk_query_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1M1S77R2A1S0S76S16G0R2A2Zd6A3S0G1S6R5U0A2S17G0Z0A2A3S87S1bVsegs;R6R4A3R5A2F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 Hi Hno Hq.
    eapply only_ok_ret; [intros R; exact (@brk_query_inv (sys_input segs ms x8) m R Hno Hq)| exact Hi].
  Qed.

  Lemma wstep_brk_grow_inv : ltac2:(tb__ "0|7|
S29S36A1M0S7S37S15Q40M1A1M2S78S0S28G2A1S8R4A1S2aG2R2A2A3S77R4A1S0S76S16G1R4A2Zd6A3S8dS16G1S57S41R6A1M3A1A2S16G1S47G3A1A2A2S8fS16G1S47S41R7A1A1A2S16G1S6R8U0M4A2A2A2S79Vsegs;S27G0S1aRaS19R9R8A2A4R6A3S3S1S0S2bSa6R9S6RaG4A2M5G5A3S30A3S0S78R7S27G0S1aRbS19S7fRaG5S83RaSb2S41R9A1M6G5G5A3A2A3S54Sa7G6G5G5A3R9A2A2A4A3A2S0S78R7S27G0S1aRbS19S7eRaS47G6A1A2R9A2A4A3A2F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp [Hh Hl] Hno Hsb Hlt Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@brk_grow_inv (sys_input segs ms x8) m _ Hno Hsb Hlt) in Hspec.
    destruct Hspec as [(Hg & E) | E]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact Hg|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|msimp Hcd; congruence].
      mat_id Hm Hl.
      rewrite advance_apply_effect, app_nil_r by reflexivity. reflexivity.
    - right. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      mat_id Hm Hl. now rewrite app_nil_r.
  Qed.

  Lemma wstep_brk_grow_intro_ok : ltac2:(tb__ "0|8|
S29S36A1M0S7S37S15Q40M1A1M2S0S28G2A1S8R3A1S2aG2R1A2A3S77R3A1S0S76S16G1R3A2Zd6A3S8dS16G1S57S41R5A1M3A1A2S16G1S47G3A1A2A2S8fS16G1S47S41R6A1A1A2S16G1S6R7U0M4A2A2A2S0S2bSa6R7S6R8G4A2M5G5A3S30A3S79Vsegs;S27G0S1aRaS19R9R8A2A4S27G0S1aRaS19S7fR9S6R9G4A2M6S83R9Sb2S41R8A1M7G6G6A3A2A3S54Sa7G7G6G6A3R8A2A2A4A3F_;F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hsb Hlt Hg.
    pose proof (@brk_grow_intro_ok (sys_input segs ms x8) m Hno Hsb Hlt Hg) as Hs.
    pose proof (@wstep_pending_run0 tr _ _ _ _ _ Hp (model_idle_halted Hi) Hs
                  ltac:(destruct Hi as [H1 H2]; split; assumption)) as W.
    rewrite advance_apply_effect in W by reflexivity. exact W.
  Qed.

  Lemma wstep_brk_grow_intro_fail : forall tr ms m x8,
    ms_svc_pending ms = Some x8 -> model_idle m -> bv_unsigned x8 = 214%Z ->
    (bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned (vm_brk (m_vmmaps m)))%Z ->
    (bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned (ms_gpr ms 0))%Z ->
    brk_grow_ok m (ms_gpr ms 0) (ms_gpr ms 0) = false ->
    wstep (tr, mkCfg ms m) (tr, mkCfg (after_sys ms (vm_brk (m_vmmaps m))) m).
  Proof using .
    intros tr ms m x8 Hp Hi Hno Hsb Hlt Hg. refine (@wstep_ret_intro0 tr _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    exact (@brk_grow_intro_fail_ns (sys_input segs ms x8) m Hno Hsb Hlt Hg).
  Qed.

  Lemma brk_grow_only_ok : ltac2:(tb__ "0|2|
S7S37S15Q40M0A1S77R2A1S0S76S16G0R2A2Zd6A3S8dS16G0S57S41R4A1M1A1A2S16G0S47G1A1A2A2S8fS16G0S47S41R5A1A1A2S16G0S6R6U0A2A2A2S87S1bVsegs;R7R5A3R6A2F_;F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 [Hh Hl] Hno Hsb Hlt.
    eapply only_ok_of_inv; [intros R; exact (@brk_grow_inv (sys_input segs ms x8) m R Hno Hsb Hlt)| |].
    - intros [(_ & E) | E]; unfold is_ret in E; discriminate.
    - intros eff m' evs [(_ & E) | E] _; unfold is_ret in E; inversion E; subst; exact Hl.
  Qed.

End WithImage.
