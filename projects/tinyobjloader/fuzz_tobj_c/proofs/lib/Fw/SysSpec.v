(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "iff"; "not"; "False"; "@Corelib.Init.Datatypes"; "nil"; "prod"; "list"; "bool"; "cons"; "nat"; "true"; "option"; "pair"; "false"; "length"; "Some"; "andb"; "None"; "app"; "negb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_and"; "bv_add"; "bv_sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "SyscallEffect"; "event"; "Model"; "m_vmmaps"; "in_arg"; "MemCopy"; "mkEffectU"; "FdEntry"; "errno_ret"; "vm_init_sp"; "m_fds"; "in_mem"; "VmMaps"; "fd_lookup"; "vm_brk"; "cstr_result"; "read_cstr"; "vm_maps"; "CstrOk"; "SyscallInput"; "m_vm_lazy"; "page_size"; "WriteEv"; "alloc_fd"; "alloc_top"; "vm_reserved"; "m_fs"; "with_fds"; "vm_noaccess"; "vm_start_brk"; "ENOMEM"; "with_vmmaps"; "EBADF"; "access_okb"; "region_free"; "vm_forget_range"; "TASK_SIZE"; "in_sysno"; "mkVmMapsFull"; "vm_limit"; "ENOENT"; "FdChannel"; "fd_insert"; "map_contains"; "read_bytes_map"; "vm_mmap_base"; "m_tid"; "map_has"; "with_tid"; "FdFile"; "InputStream"; "maps_subtract"; "with_halted"; "FdDir"; "two_pow_64"; "with_fs"; "with_stdin"; "CstrFault"; "CstrTooLong"; "EFAULT"; "EINVAL"; "EISDIR"; "ENAMETOOLONG"; "ENOTTY"; "IOV_MAX"; "MAX_RW_COUNT"; "addr_is_error_b"; "iovs_total"; "m_halted"; "sp_window_hi"; "sp_window_lo"; "ImpOk"; "ProcInput"; "in_wmem"; "init_model"; "iov_import"; "iovs_access_okb"; "m_stdin"; "read_u64"; "stack_max_size"; "cap_iovecs_aux"; "copy_iovecs_accesses"; "copy_iovecs_aux"; "cstr_access_len_aux"; "eff_copyins"; "fd_remove"; "gather_prefix"; "import_iovecs"; "import_iovecs_accesses"; "iov_prefix_accesses"; "m_vm_materialized"; "map_remove"; "page_round_up_Z"; "path_max"; "rw_count_clamp"; "vm_add_lazy"; "vm_backing_used"; "with_vm_backing"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude"; "check_result"; "CheckReject"; "CheckOk"; "check_ret_only"; "CheckUnmodeled"; "errno_ret_in"; "listNN_eqb"; "check_copyins_after"; "check_ret_only_copyins"; "access_ranges_eqb"; "clear_copyins"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "Unmodeled"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "lt"; "modulo"; "leb"; "eqb"; "pow"; "sub"; "ltb"; "mul"; "to_nat"; "testbit"; "ldiff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "init_sp_ok"; "is_ret"; "mmap_nZ"; "is_ret_ci"; "mmap_n"; "exit_model"; "mmap_none_model"; "mmap_rw_model"; "brk_eff"; "mmap_fixed_ok_model"; "mmap_place_ok"; "mmap_place_ok_none"; "iovecs_at"; "iovecs_readable"; "munmap_model"; "mmap_fixed_dead_model"; "alloc_ceiling_hi"; "alloc_ceiling_lo"; "iov_desc_accesses"; "mmap_fixed_dead_vm"; "writev_reads"; "check_of"; "mmap_fixed_ok_vm"; "mmap_none_vm"; "mmap_rw_vm"; "munmap_vm"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs"; "check_syscall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.Openat"; "openat_reads"; "openat_dir_model"; "openat_file_model";
"@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "w_is0"; "cmd32"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open"; "check_openat_body"; "check_open_result"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open"; "path_is_dirref"; "openat_errnos"; "open_ignored_flags"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "word_to_nat"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "Fs"; "path"; "file_read"; "path_eqb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei"; "path_has_slash"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "with_brk_next"; "mmap_anon_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noaccess_b"; "mmap_off_aligned_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "brk_model_next"; "brk_r_ok"; "mmap_flags_core"; "mmap_noreserve_b"; "mmap_noreserve_backed_ok"; "munmap_free_ok"; "with_mmap_backing"; "brk_grow_ok"; "brk_unmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_errnos_when"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_noaccess_b"; "brk_zeros"; "with_mmap_destroyed"; "brk_grants"; "brk_page_range"; "forget_vm_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_destructive_errnos"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_errnos"; "mmap_fd_none"; "mmap_fixed_destroyed_next"; "with_mmap_replacement"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_model_next"; "mprotect_budget_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mprotect_errnos_when"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_grows_conflict_b"; "mprotect_modeled_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mprotect_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "TIOCGWINSZ"; "dot_path"; "AT_FDCWD32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.Writev"; "writev_reads"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite"; "iovcnt32"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.Close"; "close_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.ReadFile"; "file_read_bytes"; "read_file_eff"; "read_file_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.Writev1"; "writev1_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.Writev2"; "writev2_reads"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite"; "check_read"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork"; "check_set_tid_address"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap"; "check_brk"; "check_mmap"; "check_munmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "w_nilb"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess"; "delivered_writes"; "rw_bytes_max"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition check_of (i : SyscallInput) (m : Model) (R : outcome SyscallEffect) : Prop := ltac2:(tb__ "0|0|
S8dS1dA1OLR;VR;S1dS1fS9S1eA1S0S80Sb7Vi;R3Vm;A3S82R2R1A2A3Levs;Lm';Leff;S1dS0S80Sb7Vi;R1Vm;A3S84A3Feff;X8dx2").

Lemma spec_check : ltac2:(tb__ "0|0|
S30S1fS8dS1dA1S8bR3R2R1A3Sb2R4R3R2A3F_;FR;Fm;Fi;").
Proof.
  intros i m [eff m' evs|] H; cbn.
  - apply check_syscall_complete_ok, H.
  - intros eff. eapply check_syscall_complete_unmodeled, H.
Qed.

Lemma check_spec_ok : ltac2:(tb__ "0|0|
S30S1fS1dS1fS9S1eA1S0S80Sb7R5R3R4A3S82R2R1A2A3S8bR6R5S8cS1dR4R3R2A4A3F_;Fevs;Fm';Feff;Fm;Fi;").
Proof. intros. apply check_syscall_sound_ok. assumption. Qed.

Definition probe_eff : SyscallEffect := mkEffect (Z_to_bv 64 0) [] [].

Lemma ca_no_arm_eventfd2' : ca_no arm_eventfd2 = 19%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_epoll_create1' : ca_no arm_epoll_create1 = 20%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_epoll_ctl' : ca_no arm_epoll_ctl = 21%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_epoll_pwait' : ca_no arm_epoll_pwait = 22%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_pread64' : ca_no arm_pread64 = 67%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_pwrite64' : ca_no arm_pwrite64 = 68%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_tkill' : ca_no arm_tkill = 130%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_tgkill' : ca_no arm_tgkill = 131%Z. Proof. reflexivity. Qed.
Lemma ca_no_arm_uname' : ca_no arm_uname = 160%Z. Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_eventfd2' ca_no_arm_epoll_create1' ca_no_arm_epoll_ctl'
  ca_no_arm_epoll_pwait' ca_no_arm_pread64' ca_no_arm_pwrite64' ca_no_arm_tkill'
  ca_no_arm_tgkill' ca_no_arm_uname' : arm_unfold.

Ltac dispatch_in H Hno :=
  unfold check_syscall in H; rewrite Hno in H;
  cbn [lookup_ca checked_table] in H; autorewrite with arm_unfold in H;
  cbn [Z.eqb Pos.eqb] in H; autorewrite with arm_unfold in H.
Ltac dispatch Hno :=
  unfold check_syscall; rewrite Hno;
  cbn [lookup_ca checked_table]; autorewrite with arm_unfold;
  cbn [Z.eqb Pos.eqb]; autorewrite with arm_unfold.

Lemma ret_only_inv : ltac2:(tb__ "0|3|
S1dS17Q40A1M0S1fS9S1eA1M1S1fG1S0S80S83R6R5R4R3A4S82R2R1A2A3S1S0S1dR7S23R6S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M2G2S7S22A1S7S8G0ScA2A1A6A3S1S0S1fR3R5A3S0G1R2R4A3A2A2F_;Fevs;Fm';Fevs1;Fm1;Fr;Feff;").
Proof. intros. apply check_ret_only_ok_iff. assumption. Qed.

Lemma ret_only_refl : ltac2:(tb__ "0|2|
S17Q40A1M0S1fS9S1eA1S0S80S83S23R3S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6R3R2R1A4S82R2R1A2A3Fevs;Fm;Fr;").
Proof. intros. apply check_ret_only_ok_iff. auto. Qed.

Lemma ret_only_not_unmodeled : ltac2:(tb__ "0|0|
S1dS17Q40A1S1fS9S1eA1S0S80S83R4R3R2R1A4S84A3S6F_;Fevs;Fm;Fr;Feff;").
Proof. intros eff r m evs H. exact (check_ret_only_no_unmodeled _ _ _ _ H). Qed.

Definition is_ret (R : outcome SyscallEffect) (r : word) (m' : Model) (evs : list event) : Prop := ltac2:(tb__ "0|2|
S0S8dS1dA1VR;S8cS1dS23Vr;S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm';Vevs;A4A3").

Definition is_ret_ci (R : outcome SyscallEffect) (r : word) (ci : list (word * nat))
    (m' : Model) (evs : list event) : Prop := ltac2:(tb__ "0|2|
S0S8dS1dA1VR;S8cS1dS23Vr;S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Vci;A6Vm';Vevs;A4A3").

Lemma is_ret_is_ret_ci : ltac2:(tb__ "0|1|
S8dS1dA1S17Q40A1M0S1fS9S1eA1S9eR4R3R2R1A4Sa0R5R4S7S8G0ScA2A1R3R2A5F_;Fevs;Fm';Fr;FR;").
Proof. intros R r m' evs H. exact H. Qed.

Lemma check_of_ret_only : ltac2:(tb__ "0|0|
S30S1fS8dS1dA1S17Q40A1S1fS9S1eA1S1dS0S80Sb7R7R1R6A3S83R1R4R3R2A4A3Feff;S8bR7R6R5A3S9eR6R5R4R3A4F_;F_;Fevs1;Fm1;Fr;FR;Fm;Fi;").
Proof.
  intros i m R r m1 evs1 Hc Hs. apply spec_check in Hs.
  destruct R as [eff m' evs|]; cbn in Hs.
  - rewrite Hc in Hs. apply ret_only_inv in Hs. destruct Hs as (-> & -> & ->). reflexivity.
  - exfalso. specialize (Hs probe_eff). rewrite Hc in Hs.
    exact (ret_only_not_unmodeled _ _ _ _ Hs).
Qed.

Lemma intro_ret_only : ltac2:(tb__ "0|2|
S30S1fS17Q40A1M0S1fS9S1eA1S1dS0S80Sb7R6R1R5A3S83R1R4R3R2A4A3Feff;S8bR6R5S8cS1dS23R4S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6R3R2A4A3F_;Fevs1;Fm1;Fr;Fm;Fi;").
Proof.
  intros i m r m1 evs1 Hc. apply check_spec_ok. rewrite Hc. apply ret_only_refl.
Qed.

Lemma ret_only_copyins_inv : ltac2:(tb__ "0|3|
S9S8S17Q40A1M0ScA2A1S1dG0S1fS9S1eA1M1S1fG1S0S80S88R7R6R5R4R3A5S82R2R1A2A3S1S0S1dR7S23R6S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M2G2S7S22A1R8A6A3S1S0S1fR3R5A3S0G1R2R4A3A2A2F_;Fevs;Fm';Fevs1;Fm1;Fr;Feff;Freads;").
Proof.
  intros reads eff r m1 evs1 m' evs H.
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->). auto.
Qed.

Lemma check_of_ret_only_copyins : ltac2:(tb__ "0|1|
S30S1fS8dS1dA1S9S8S17Q40A1M0ScA2A1G0S1fS9S1eA1S1dS0S80Sb7R8R1R7A3S88R5R1R4R3R2A5A3Feff;S8bR8R7R6A3Sa0R7R5R6R4R3A5F_;F_;Fevs1;Fm1;Fr;Freads;FR;Fm;Fi;").
Proof.
  intros i m R reads r m1 evs1 Hc Hs. apply spec_check in Hs.
  destruct R as [eff m' evs|]; cbn in Hs.
  - rewrite Hc in Hs. apply ret_only_copyins_inv in Hs. destruct Hs as (-> & -> & ->). reflexivity.
  - exfalso. specialize (Hs probe_eff). rewrite Hc in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

Lemma intro_ret_only_copyins : ltac2:(tb__ "0|2|
S30S1fS9S8S17Q40A1M0ScA2A1G0S1fS9S1eA1S1dS0S80Sb7R7R1R6A3S88R5R1R4R3R2A5A3Feff;S8bR7R6S8cS1dS23R4S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1R5A6R3R2A4A3F_;Fevs1;Fm1;Fr;Freads;Fm;Fi;").
Proof.
  intros i m reads r m1 evs1 Hc. apply check_spec_ok. rewrite Hc.
  apply check_ret_only_copyins_refl.
Qed.

Lemma with_vmmaps_eta : ltac2:(tb__ "0|1|
S1fS0S1fS3cS43S36S20R1A1M0A1S2eG0A1S39G0A1S3aG0A1S2bG0A1S44G0A1S4aG0A1S26G0A1A8R1A2R1A3Fm;").
Proof. intros m. destruct m as [fds vm io fs pr lm tm]; destruct vm as [h lz mt]; destruct h; reflexivity. Qed.

Lemma with_vmmaps_m_vmmaps : ltac2:(tb__ "0|0|
S1fS0S1fS3cS20R1A1R1A2R1A3Fm;").
Proof. intros m. destruct m as [fds vm io fs pr lm tm]; destruct vm; reflexivity. Qed.

Lemma m_vm_lazy_with_fds : ltac2:(tb__ "0|1|
S9S8S17Q40A1M0S24A2A1S1fS0S9S8G0G0A2A1S31S38R2R1A2A1S31R1A1A3Fm;Ff;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : ltac2:(tb__ "0|1|
S29S1fS0S9S8S17Q40A1M0G0A2A1S31S3cR2R1A2A1S31R1A1A3Fm;Fh;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_stdin : ltac2:(tb__ "0|1|
S4fS1fS0S9S8S17Q40A1M0G0A2A1S31S55R2R1A2A1S31R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_fs : ltac2:(tb__ "0|1|
ScaS1fS0S9S8S17Q40A1M0G0A2A1S31S54R2R1A2A1S31R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_halted : ltac2:(tb__ "0|1|
S17Q40A1M0S1fS0S9S8G0G0A2A1S31S51R2R1A2A1S31R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_tid : ltac2:(tb__ "0|1|
S17Q40A1M0S1fS0S9S8G0G0A2A1S31S4dR2R1A2A1S31R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_fds m_vm_lazy_with_vmmaps m_vm_lazy_with_stdin
  m_vm_lazy_with_fs m_vm_lazy_with_halted m_vm_lazy_with_tid : model.

Lemma m_halted_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0SeS17Q40A1A1S61S40R3R2R1A3A1S61R1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
Lemma m_fds_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0S9S8S17Q40A1S24A2A1S27S40R3R2R1A3A1S27R1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
Lemma m_fs_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0ScaS37S40R3R2R1A3A1S37R1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0S29S20S40R3R2R1A3A1S20R1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
Lemma m_tid_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0SeS17Q40A1A1S4bS40R3R2R1A3A1S4bR1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
Lemma m_stdin_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0S4fS6aS40R3R2R1A3A1S6aR1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_vm_forget_range m_fds_vm_forget_range m_fs_vm_forget_range
  m_vmmaps_vm_forget_range m_tid_vm_forget_range m_stdin_vm_forget_range : model.

Lemma maps_subtract_nil : ltac2:(tb__ "0|3|
S7fS7fS0S9S8S17Q40A1M0G0A2M1A1S50S7G1A1M2R2R1A3G2A3Fhi;Flo;").
Proof. reflexivity. Qed.

Lemma m_vm_lazy_vm_forget_range : ltac2:(tb__ "0|4|
S7fS7fS1fS0S9S8S17Q40A1M0G0A2M1A1M2S31R1A1S7G1A1M3A3S0G2S31S40R4R3R2A3A1G3A3F_;Fm;Fhi;Flo;").
Proof.
  intros lo hi m H. destruct m as [fds vm io fs pr lm tm]; destruct vm as [h lz mt].
  cbn in H |- *. subst lz. reflexivity.
Qed.

Lemma vm_forget_range_id : ltac2:(tb__ "0|2|
S7fS7fS1fS0S9S8S17Q40A1M0G0A2M1A1S31R1A1S7G1A1A3S0S9G0A1S77R2A1S7G0A1A3S0S1fS40R5R4R3A3R3A3F_;F_;Fm;Fhi;Flo;").
Proof.
  intros lo hi m H1 H2. destruct m as [fds vm io fs pr lm tm]; destruct vm as [h lz mt].
  cbn in H1, H2 |- *. subst. reflexivity.
Qed.

Definition exit_model (i : SyscallInput) (m : Model) : Model := ltac2:(tb__ "0|1|
S51S1aQ40M0S21Vi;U0A2S19G0ZffA2A3Vm;A2").

Lemma exit_check : ltac2:(tb__ "0|2|
S30S1fS1dS3S0S7fS18Q40M0S42R3A1A2M1Z5dA3S0S7fG1Z5eA3A2S0S80Sb7R4R2R3A3S83R2S19G0Z0A2Sa2R4R3A2S7S1eA1A4A3F_;Feff;Fm;Fi;").
Proof.
  intros i m eff [Hno|Hno]; dispatch Hno; reflexivity.
Qed.

Lemma exit_inv : ltac2:(tb__ "0|2|
S30S1fS8dS1dA1S3S0S7fS18Q40M0S42R3A1A2M1Z5dA3S0S7fG1Z5eA3A2S8bR4R3R2A3S9eR3S19G0Z0A2Sa2R5R4A2S7S1eA1A4F_;F_;FR;Fm;Fi;").
Proof. intros i m R Hno. apply check_of_ret_only. intros; apply exit_check, Hno. Qed.

Lemma exit_intro_ss : ltac2:(tb__ "0|4|
S30S1fS3S0S7fS18Q40M0S42R2A1A2M1Z5dA3S0S7fG1Z5eA3A2S8bR3R2S8cS1dS23S19G0Z0A2S7S8S17G0A1M2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1S7S8G2ScA2A1A6Sa2R3R2A2S7S1eA1A4A3F_;Fm;Fi;").
Proof. intros i m Hno. apply intro_ret_only. intros; apply exit_check, Hno. Qed.

Lemma exit_intro : ltac2:(tb__ "0|4|
S30S1fS3S0S7fS18Q40M0S42R2A1A2M1Z5dA3S0S7fG1Z5eA3A2S106R3R2S8cS1dS23S19G0Z0A2S7S8S17G0A1M2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1S7S8G2ScA2A1A6Sa2R3R2A2S7S1eA1A4A3F_;Fm;Fi;").
Proof.
  intros. split; [eapply exit_intro_ss; eassumption|].
  intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
Qed.

Lemma exit_model_halted : ltac2:(tb__ "0|2|
S30S1fS0SeS17Q40M0A1M1A1S61Sa2R2R1A2A1S12G1S1aG0S21R2U0A2S19G0ZffA2A3A2A3Fm;Fi;").
Proof. reflexivity. Qed.

Lemma exit_model_fs : ltac2:(tb__ "0|0|
S30S1fS0ScaS37Sa2R2R1A2A1S37R1A1A3Fm;Fi;").
Proof. reflexivity. Qed.

Lemma len_word_of_read : ltac2:(tb__ "0|3|
S17Q40A1M0SeS17Q8A1M1A1F_;G0G0S9G1A1M2S0SeG2A1S49R4R3R2A3S12G2R1A2A3S0G0Sc6G1R2A2R3A3F_;Fbs;Flen;Fa;Fmp;").
Proof.
  intros mp a len bs H. unfold len_word.
  rewrite (read_bytes_map_length _ _ _ _ H). apply Z_to_bv_bv_unsigned.
Qed.

Lemma w_is0_spec : ltac2:(tb__ "0|2|
S17Q40M0A1M1S4S0SaSbcR1A1SdA3S0G1R1S19G0Z0A2A3A2Fw;").
Proof. intros w. unfold w_is0. apply bv_eqb_eq. Qed.

Lemma w_is0_false : ltac2:(tb__ "0|1|
S17Q40M0A1S4S0SaSbcR1A1S10A3S5S0S7fS18G0R1A2Z0A3A1A2Fw;").
Proof.
  intros w. unfold w_is0. split.
  - intros H Hz. enough (bv_eqb w (Z_to_bv 64 0) = true) by congruence.
    apply bv_eqb_eq. apply bv_eq. rewrite Hz. reflexivity.
  - intros H. destruct (bv_eqb w (Z_to_bv 64 0)) eqn:E; [|reflexivity].
    exfalso. apply bv_eqb_eq in E. subst. apply H. reflexivity.
Qed.

Lemma len_word_unsigned : ltac2:(tb__ "0|1|
S9S17Q8A1M0A1S92S90S11G0R1A2A1S53A2S0S7fS18Q40Sc6G0R2A2A2S90S11G0R2A2A1A3F_;Fbs;").
Proof.
  intros bs H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus, two_pow_64 in *. change (Z.of_N 64) with 64%Z. lia.
Qed.

Lemma len_word_firstn_to_nat : ltac2:(tb__ "0|1|
S9S17Q8A1M0A1ScSbeR1S11G0R2A2A2S92S90S11G0R3A2A1S53A2S0ScS9aS18Q40Sc6G0Sc0G0R3R4A3A2A2A1R3A3F_;F_;Fn;Fbs;").
Proof.
  intros bs n Hn Hlen. rewrite len_word_unsigned.
  - rewrite length_firstn, Nat.min_l by exact Hn. apply Nat2Z.id.
  - rewrite length_firstn. lia.
Qed.

Section Write.
  Variables (i : SyscallInput) (m : Model) (ch : word) (bs : list byte).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 64%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46Vch;A1A2A3").
  Hypothesis Hch : ch <> Z_to_bv 64 0.

  Hypothesis Hbuf : ltac2:(tb__ "0|1|
S0SeS9S17Q8A1A1M0A1S49S28Vi;A1S21Vi;U1A2S21Vi;U2A2A3S12G0Vbs;A2A3").
  Hypothesis Hpos : (0 < bv_unsigned (in_arg i 2))%Z.
  Hypothesis Hmax : ltac2:(tb__ "0|0|
S8fS18Q40S21Vi;U2A2A2S104A2").

  Let buf := in_arg i 1.

  Lemma write_len : ltac2:(tb__ "0|0|
S0S7fS90S11S17Q8A1Vbs;A2A1S18Q40S21Vi;U2A2A2A3").
  Proof using Hbuf. exact (read_bytes_map_length _ _ _ _ Hbuf). Qed.

  Lemma write_check : ltac2:(tb__ "0|d|
S1dS0S80Sb7Vi;R1Vm;A3S1dS80Leff;R1S17Q40M0A1M1S9S8G1S9S17Q8A1M2A1A2M3A1M4S9S8G1G1A2M5A1M6G6S9S22A1M7S9S8G1ScA2M8A1G4S80Leff_writes;R5G6S80Leff_zeros;R4G6S80Leff_unmaps;R3G7S80Leff_copies;R2SaS80L_;M9S13S94Z1S18G0R6A2MaA2S94GaS90S11G2Vbs;A2A1A2A2G9S89R1SbG8SfG1ScVbuf;S9aGaA1MbA4S7G8A1A3A2S82Vm;SbfG2S1eS33Vch;A1Sc0G2GbVbs;A3A4A2S81Xax2S81Xax2S22G7S81Ll;Lm0;X9x2G5G6S81Ll;Lp;McX9x2GcX9x2G3G4S81Ll;Lp;X9x2Lcopyins;Leff_copies;Leff_unmaps;Leff_zeros;Leff_writes;Lret;X1dx1A3Feff;").
  Proof using Hbuf Hch Hfd Hmax Hno Hpos.
    intros eff. dispatch Hno. unfold check_write. rewrite Hfd.
    destruct (w_is0 ch) eqn:E; [apply w_is0_spec in E; contradiction|].
    rewrite (rw_range_in_range _ _ Hmax).
    rewrite (w_is0_pos _ Hpos).
    cbv zeta. rewrite (write_source_of_rw _ _ _ Hmax).
    rewrite (readable_bytes_full _ _ _ _ Hbuf).
    pose proof write_len as L.
    destruct (Nat.eqb (length bs) 0) eqn:En; [apply Nat.eqb_eq in En; lia|].
    reflexivity.
  Qed.

  Lemma write_inv : ltac2:(tb__ "0|4|
S8dS1dA1S8bVi;Vm;R1A3S2ScScS1S1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs;A2A2A2Sa0R3S19Q40M1S90R1A1A2SbS8S17G1A1M2ScA2M3SfG2ScVbuf;R1A4S7G3A1A3Vm;SbfG0S1eS33Vch;A1Sc0G0R1Vbs;A3A4A5A2Lk;A2F_;FR;").
  Proof using Hbuf Hch Hfd Hmax Hno Hpos.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite write_check in Hs. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct us; [|discriminate]. destruct cs; [|discriminate].
      match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G; [|discriminate] end.
      match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G3; [|discriminate] end.
      apply andb_true_iff in G as [G1 G2].
      apply Z.leb_le in G1. apply Z.leb_le in G2. apply access_ranges_eqb_eq in G3. subst ci.
      inversion Hs; subst. exists (Z.to_nat (bv_unsigned r)). split; [lia|].
      unfold is_ret_ci. rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite write_check in Hs. unfold probe_eff in Hs.
      cbn in Hs. discriminate.
  Qed.

  Lemma write_intro_prefix_ss : ltac2:(tb__ "0|5|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs;A2A2A2S8bVi;Vm;S8cS1dS23S19Q40M1S90R2A1A2S7S8S17G1A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1SbS8G2ScA2M4SfG2ScVbuf;R2A4S7G4A1A3A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2Vbs;A3A4A4A3F_;Fk;").
  Proof using Hbuf Hch Hfd Hmax Hno Hpos.
    intros k Hk. apply check_spec_ok. rewrite write_check.
    pose proof write_len as L. pose proof (word_unsigned_range (in_arg i 2)) as Hr.
    assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
    { apply Z_to_bv_small. unfold bv_modulus. change (Z.of_N 64) with 64%Z. unfold two_pow_64 in Hr. lia. }
    rewrite Hu, Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma write_intro_prefix : ltac2:(tb__ "0|5|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs;A2A2A2S106Vi;Vm;S8cS1dS23S19Q40M1S90R2A1A2S7S8S17G1A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1SbS8G2ScA2M4SfG2ScVbuf;R2A4S7G4A1A3A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2Vbs;A3A4A4A3F_;Fk;").
  Proof using Hbuf Hch Hfd Hmax Hno Hpos.
    intros. split; [eapply write_intro_prefix_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma write_intro_ss : ltac2:(tb__ "0|4|
S8bVi;Vm;S8cS1dS23S21Vi;U2A2S7S8S17Q40A1M0S9S17Q8A1M1A1A2A1S7S8G0G0A2A1M2G2S7S22A1SbS8G0ScA2M3SfG0ScVbuf;S11G1Vbs;A2A4S7G3A1A3A6Vm;SbfG1S1eS33Vch;A1Vbs;A4A4A3").
  Proof using Hbuf Hch Hfd Hmax Hno Hpos.
    pose proof (write_intro_prefix (length bs)) as H.
    rewrite firstn_all, write_len, Z_to_bv_bv_unsigned in H. apply H.
    pose proof write_len as L. lia.
  Qed.

  Lemma write_intro : ltac2:(tb__ "0|4|
S106Vi;Vm;S8cS1dS23S21Vi;U2A2S7S8S17Q40A1M0S9S17Q8A1M1A1A2A1S7S8G0G0A2A1M2G2S7S22A1SbS8G0ScA2M3SfG0ScVbuf;S11G1Vbs;A2A4S7G3A1A3A6Vm;SbfG1S1eS33Vch;A1Vbs;A4A4A3").
  Proof using Hbuf Hch Hfd Hmax Hno Hpos.
    intros. split; [eapply write_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End Write.

Section Close.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 57%Z.

  Definition close_model : Model := ltac2:(tb__ "0|0|
S38S72S27Vm;A1SbbS21Vi;U0A2A1A2Vm;A2").

  Lemma close_check_live : ltac2:(tb__ "0|0|
S24S1dS0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24R2A2A3S0S80Sb7Vi;R2Vm;A3S83R2S19Q40Z0A2Sf7S7S1eA1A4A3F_;Feff;Fe;").
  Proof using Hno. intros e eff Hfd. dispatch Hno. unfold check_close. rewrite Hfd. reflexivity. Qed.

  Lemma close_check_absent : ltac2:(tb__ "0|0|
S1dS0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S0S80Sb7Vi;R2Vm;A3S83R2S25S3dA1Vm;S7S1eA1A4A3F_;Feff;").
  Proof using Hno. intros eff Hfd. dispatch Hno. unfold check_close. rewrite Hfd. reflexivity. Qed.

  Lemma close_inv : ltac2:(tb__ "0|0|
S24S8dS1dA1S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24R2A2A3S8bVi;Vm;R2A3S9eR3S19Q40Z0A2Sf7S7S1eA1A4F_;F_;FR;Fe;").
  Proof using Hno. intros e R Hfd. apply check_of_ret_only. intros; eapply close_check_live, Hfd. Qed.

  Lemma close_intro_ss : ltac2:(tb__ "0|3|
S24S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24R1A2A3S8bVi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6Sf7S7S1eA1A4A3F_;Fe;").
  Proof using Hno. intros e Hfd. apply intro_ret_only. intros; eapply close_check_live, Hfd. Qed.

  Lemma close_intro : ltac2:(tb__ "0|3|
S24S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24R1A2A3S106Vi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6Sf7S7S1eA1A4A3F_;Fe;").
  Proof using Hno.
    intros. split; [eapply close_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma close_absent_inv : ltac2:(tb__ "0|0|
S8dS1dA1S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S8bVi;Vm;R2A3S9eR3S25S3dA1Vm;S7S1eA1A4F_;F_;FR;").
  Proof using Hno. intros R Hfd. apply check_of_ret_only. intros; apply close_check_absent, Hfd. Qed.

  Lemma close_absent_intro_ss : ltac2:(tb__ "0|2|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S8bVi;Vm;S8cS1dS23S25S3dA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hno. intros Hfd. apply intro_ret_only. intros; apply close_check_absent, Hfd. Qed.

  Lemma close_absent_intro : ltac2:(tb__ "0|2|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S106Vi;Vm;S8cS1dS23S25S3dA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hno.
    intros. split; [eapply close_absent_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End Close.

Section Ioctl.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 29%Z.

  Lemma tty_only_request_TIOCGWINSZ : tty_only_request TIOCGWINSZ = true.
  Proof using . reflexivity. Qed.

  Lemma ioctl_check_open : ltac2:(tb__ "0|1|
S17Q40A1M0S1dS0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46R2A1A2A3S0G0SbdS21Vi;U1A2A1Sf1A3S0S80Sb7Vi;R3Vm;A3S83R3S25S5cA1Vm;S7S1eA1A4A3F_;F_;Feff;Fch;").
  Proof using Hno.
    intros ch eff Hfd Hc. dispatch Hno. unfold check_ioctl. rewrite Hfd, Hc.
    rewrite tty_only_request_TIOCGWINSZ. reflexivity.
  Qed.

  Lemma ioctl_inv : ltac2:(tb__ "0|1|
S17Q40A1M0S8dS1dA1S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46R2A1A2A3S0G0SbdS21Vi;U1A2A1Sf1A3S8bVi;Vm;R3A3S9eR4S25S5cA1Vm;S7S1eA1A4F_;F_;F_;FR;Fch;").
  Proof using Hno. intros ch R Hfd Hc. apply check_of_ret_only. intros; eapply ioctl_check_open; eauto. Qed.

  Lemma ioctl_intro_ss : ltac2:(tb__ "0|2|
S17Q40A1M0S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46R1A1A2A3S0G0SbdS21Vi;U1A2A1Sf1A3S8bVi;Vm;S8cS1dS23S25S5cA1S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;F_;Fch;").
  Proof using Hno. intros ch Hfd Hc. apply intro_ret_only. intros; eapply ioctl_check_open; eauto. Qed.

  Lemma ioctl_intro : ltac2:(tb__ "0|2|
S17Q40A1M0S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46R1A1A2A3S0G0SbdS21Vi;U1A2A1Sf1A3S106Vi;Vm;S8cS1dS23S25S5cA1S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;F_;Fch;").
  Proof using Hno.
    intros. split; [eapply ioctl_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma ioctl_check_absent : ltac2:(tb__ "0|0|
S1dS0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S0S80Sb7Vi;R2Vm;A3S83R2S25S3dA1Vm;S7S1eA1A4A3F_;Feff;").
  Proof using Hno. intros eff Hfd. dispatch Hno. unfold check_ioctl. rewrite Hfd. reflexivity. Qed.

  Lemma ioctl_absent_inv : ltac2:(tb__ "0|0|
S8dS1dA1S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S8bVi;Vm;R2A3S9eR3S25S3dA1Vm;S7S1eA1A4F_;F_;FR;").
  Proof using Hno. intros R Hfd. apply check_of_ret_only. intros; apply ioctl_check_absent, Hfd. Qed.

  Lemma ioctl_absent_intro_ss : ltac2:(tb__ "0|2|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S8bVi;Vm;S8cS1dS23S25S3dA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hno. intros Hfd. apply intro_ret_only. intros; apply ioctl_check_absent, Hfd. Qed.

  Lemma ioctl_absent_intro : ltac2:(tb__ "0|2|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3S106Vi;Vm;S8cS1dS23S25S3dA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hno.
    intros. split; [eapply ioctl_absent_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End Ioctl.

Lemma fd32_lit : ltac2:(tb__ "0|2|
S7fS1S8fZ0R1A2S92R1S96Z2Z20A2A2A2S0S17Q40M0A1SbbS19G0R2A2M1A1G1A3F_;Fz;").
Proof.
  intros z Hz. apply fd32_id. rewrite Z_to_bv_small; [lia|].
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

Lemma fd32_alloc_fd : ltac2:(tb__ "0|2|
S9S8S17Q40A1M0S24A2A1S0G0SbbS34R1A1M1A1G1A3Ffds;").
Proof.
  intros fds. apply fd32_id. pose proof (alloc_fd_le fds).
  pose proof (word_unsigned_range (alloc_fd fds)). lia.
Qed.

Lemma cmd32_TIOCGWINSZ : ltac2:(tb__ "0|2|
S17Q40M0A1M1S0S7fS93S18G0R1A2S96Z2Z20A2A2Z5413A3S0G1SbdR2A1Sf1A3F_;Fw;").
Proof. intros w H. unfold cmd32, abi_low32. rewrite H. reflexivity. Qed.

Section SetTid.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 96%Z.

  Lemma set_tid_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3SfeR1Vm;A2A3Feff;").
  Proof using Hno. intros eff. dispatch Hno. reflexivity. Qed.

  Lemma set_tid_fresh_inv : ltac2:(tb__ "0|3|
S8dS1dA1S0SeS17Q40M0A1M1A1S4bVm;A1S14G1A1A3S8bVi;Vm;R2A3S2G1G1S1S1S92Z0S18G0R1A2M2A2S92G2Sf6A2A2S9eR4R1S4dR1Vm;A2S7S1eA1A4A2Ltid;A2F_;F_;FR;").
  Proof using Hno.
    intros R Ht Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite set_tid_check in Hs. unfold check_set_tid_address in Hs.
      destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Ht in Hs.
      destruct ((0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z) eqn:E;
        [|discriminate].
      apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      inversion Hs; subst. exists r. split; [lia|reflexivity].
    - exfalso. specialize (Hs probe_eff). rewrite set_tid_check in Hs.
      unfold check_set_tid_address, probe_eff in Hs. rewrite Ht in Hs.
      cbn in Hs. discriminate.
  Qed.

  Lemma set_tid_fresh_intro_ss : ltac2:(tb__ "0|4|
S17Q40M0A1M1S0SeG1A1S4bVm;A1S14G1A1A3S1S92Z0S18G0R2A2M2A2S92G2Sf6A2A2S8bVi;Vm;S8cS1dS23R3S7S8G1S9S17Q8A1A1A2A1S7S8G1G1A2A1M3G3S7S22A1S7S8G1ScA2A1A6S4dR3Vm;A2S7S1eA1A4A3F_;F_;Ftid;").
  Proof using Hno.
    intros tid Ht Hr. apply check_spec_ok. rewrite set_tid_check.
    unfold check_set_tid_address. rewrite Ht.
    replace ((0 <? bv_unsigned tid)%Z && (bv_unsigned tid <? PID_MAX_ENVELOPE)%Z) with true;
      [reflexivity|].
    symmetry. apply andb_true_iff. split; apply Z.ltb_lt; lia.
  Qed.

  Lemma set_tid_fresh_intro : ltac2:(tb__ "0|4|
S17Q40M0A1M1S0SeG1A1S4bVm;A1S14G1A1A3S1S92Z0S18G0R2A2M2A2S92G2Sf6A2A2S106Vi;Vm;S8cS1dS23R3S7S8G1S9S17Q8A1A1A2A1S7S8G1G1A2A1M3G3S7S22A1S7S8G1ScA2A1A6S4dR3Vm;A2S7S1eA1A4A3F_;F_;Ftid;").
  Proof using Hno.
    intros. split; [eapply set_tid_fresh_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma set_tid_known_inv : ltac2:(tb__ "0|1|
S17Q40A1M0S8dS1dA1S0SeG0A1S4bVm;A1S12G0R2A2A3S8bVi;Vm;R2A3S9eR3R4Vm;S7S1eA1A4F_;F_;FR;Ft;").
  Proof using Hno.
    intros t R Ht Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite set_tid_check in Hs. unfold check_set_tid_address in Hs.
      destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Ht in Hs. destruct (bv_eqb r t) eqn:E; [|discriminate].
      apply bv_eqb_eq in E. inversion Hs; subst. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite set_tid_check in Hs.
      unfold check_set_tid_address, probe_eff in Hs. rewrite Ht in Hs.
      destruct (bv_eqb (Z_to_bv 64 0) t); discriminate.
  Qed.

  Lemma set_tid_known_intro_ss : ltac2:(tb__ "0|2|
S17Q40A1M0S0SeG0A1S4bVm;A1S12G0R1A2A3S8bVi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;Ft;").
  Proof using Hno.
    intros t Ht. apply check_spec_ok. rewrite set_tid_check.
    unfold check_set_tid_address. rewrite Ht, bv_eqb_refl. reflexivity.
  Qed.

  Lemma set_tid_known_intro : ltac2:(tb__ "0|2|
S17Q40A1M0S0SeG0A1S4bVm;A1S12G0R1A2A3S106Vi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;Ft;").
  Proof using Hno.
    intros. split; [eapply set_tid_known_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End SetTid.

Lemma one_tid_ok : ltac2:(tb__ "0|2|
S1S92Z0S18Q40M0S19G0Z1A2A2M1A2S92G1Sf6A2A2").
Proof. vm_compute. split; reflexivity. Qed.

Lemma open_result_inv : ltac2:(tb__ "0|9|
S1dS1fS17Q40A1M0S1fF_;S1fS9S1eA1M1S0S80Sc2R5R4R3A3S82R2R1A2A3S3S2S7fS7fS1Sc8S7fR1Sc4A3S1S0S1dR7S23S25R1A1S7S8G0S9S17Q8A1A1A2A1M2S7S8G0G0A2A1M3G3S7S22A1M4S7S8G0ScA2A1M5A6A3S1S0S1fR4R6A3S0G1R3S7S1eA1M6A3A2A2A2Le;A2S1S0SeS24A1S2aS27R5A1M7S34G7A1M8A2S14S24A1A3S1S0S1dR6S23G8G2G3G3G4G5A6A3S1S0S1fR3R4G8A1A3S0G1R2G6A3A2A2A2A2F_;Fevs;Fm';Fmk;Fm;Feff;").
Proof.
  intros [r ws zs us cs ci] m mk m' evs H. unfold check_open_result, check_new_fd_result in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (errno_ret_in openat_errnos r) eqn:E.
  - left. apply errno_ret_in_true in E as (e & Hin & ->). inversion H; subst.
    exists e. auto.
  - right. destruct (fd_lookup (m_fds m) r) eqn:L; [discriminate|].
    destruct (bv_eqb r (alloc_fd (m_fds m))) eqn:Q; [|discriminate].
    apply bv_eqb_eq in Q. subst r. inversion H; subst. auto.
Qed.

Lemma open_result_not_unmodeled : ltac2:(tb__ "0|0|
S1dS1fS17Q40A1S1fF_;S0S80Sc2R3R2R1A3S84A3S6F_;Fmk;Fm;Feff;").
Proof.
  intros [r ws zs us cs ci] m mk H. unfold check_open_result, check_new_fd_result in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (errno_ret_in openat_errnos r); [discriminate|].
  destruct (fd_lookup (m_fds m) r); [discriminate|].
  destruct (bv_eqb r (alloc_fd (m_fds m))); discriminate.
Qed.

Lemma open_result_intro_err : ltac2:(tb__ "0|2|
S7fS1fS17Q40A1M0S1fF_;Sc8S7fR3Sc4A3S0S80Sc2S23S25R4A1S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6R3R2A3S82R3S7S1eA1A2A3F_;Fmk;Fm;Fe;").
Proof.
  intros e m mk Hin. unfold check_open_result, check_new_fd_result.
  rewrite (errno_ret_in_intro _ _ Hin). reflexivity.
Qed.

Lemma openat_errnos_ok : errnos_ok openat_errnos = true.
Proof. reflexivity. Qed.

Lemma open_result_intro_ok : ltac2:(tb__ "0|4|
S1fS17Q40A1M0S1fF_;S0SeS24A1S2aS27R2A1M1S34G1A1A2S14S24A1A3S0S80Sc2S23S34S27R3A1A1M2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M3G3S7S22A1S7S8G0ScA2A1A6R3R2A3S82R2G2A1S7S1eA1A2A3F_;Fmk;Fm;").
Proof.
  intros m mk Hfree. unfold check_open_result, check_new_fd_result.
  rewrite (errno_ret_in_alloc_fd _ _ openat_errnos_ok), Hfree, bv_eqb_refl. reflexivity.
Qed.

Lemma clear_copyins_eq : ltac2:(tb__ "0|3|
S17Q40A1M0S9S8G0S9S17Q8A1A1A2A1S9S8G0G0A2A1M1G1S9S22A1S9S8G0ScA2M2A1S0S1dS8aS23R6R5R4R3R2R1A6A1S23R6R5R4R3R2S7G2A1A6A3Fci;Fcs;Fus;Fzs;Fws;Fr;").
Proof. reflexivity. Qed.

Lemma copyins_after_ok : ltac2:(tb__ "0|2|
S9S8S17Q40A1ScA2A1M0S1dS80S1fS9S1eA1S4S0S80S87R5R4R3A3S82R2R1A2M1A3S1S0G0S71R4A1R5A3S0S80R3G1A3A2A2Fevs;Fm';Fres;Feff;Freads;").
Proof.
  intros reads eff res m' evs. destruct res as [m1 e1| |]; cbn.
  - unfold check_copyins. destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:E.
    + apply access_ranges_eqb_eq in E. split; [intros H; inversion H; subst; auto | intros [_ ->]; reflexivity].
    + split; [discriminate|]. intros [H _]. rewrite H, (proj2 (access_ranges_eqb_eq _ _) eq_refl) in E. discriminate.
  - unfold check_copyins. destruct (access_ranges_eqb (eff_copyins eff) reads); split; try discriminate; intros [_ H]; discriminate.
  - split; [discriminate | intros [_ H]; discriminate].
Qed.

Lemma copyins_after_unmodeled : ltac2:(tb__ "0|0|
S9S8S17Q40A1ScA2A1S1dS80S0S80S87R3R2R1A3S84A3S0S80R2S84A3F_;Fres;Feff;Freads;").
Proof.
  intros reads eff [m1 e1| |] H; cbn in H; try reflexivity;
    unfold check_copyins in H; destruct (access_ranges_eqb (eff_copyins eff) reads); discriminate.
Qed.

Section Openat.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 56%Z.

  Hypothesis Hfl : ltac2:(tb__ "0|0|
S0S7fS9cS18Q40S21Vi;U2A2A2Sc5A2Z0A3").

  Let dirfd := fd32 (in_arg i 0).
  Let pathp := in_arg i 1.

  Definition openat_reads : list (word * nat) := ltac2:(tb__ "0|2|
SbS8S17Q40A1M0ScA2M1SfG0ScVpathp;S70S28Vi;A1Vpathp;S7aA3A4S7G1A1A3").

  Lemma openat_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3S87Sb8R1Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2S8aR1A1Vm;A6A3A3Feff;").
  Proof using Hfl Hno.
    intros eff. dispatch Hno. unfold check_openat.
    rewrite (modeled_open_flags_rd _ Hfl). reflexivity.
  Qed.

  Lemma openat_ret_inv : ltac2:(tb__ "0|1|
S8dS1dA1S17Q40A1S1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6S83R1R2Vm;S7S1eA1M0A4A3Feff;S8bVi;Vm;R3A3Sa0R4R3Sb8Vm;G0A5F_;F_;Fr;FR;").
  Proof using Hfl Hno.
    intros R r Hb Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite openat_check, Hb in Hs. apply copyins_after_ok in Hs as [Hci Hr].
      apply ret_only_inv in Hr as (He & -> & ->). destruct eff as [r0 ws zs us cs ci].
      rewrite clear_copyins_eq in He. inversion He; subst. cbn in Hci. subst. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite openat_check, Hb in Hs.
      apply copyins_after_unmodeled in Hs. exact (ret_only_not_unmodeled _ _ _ _ Hs).
  Qed.

  Lemma openat_ret_intro_ss : ltac2:(tb__ "0|3|
S17Q40A1M0S1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6S83R1R2Vm;S7S1eA1M1A4A3Feff;S8bVi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M2G2S7S22A1Sb8A6Vm;G1A4A3F_;Fr;").
  Proof using Hfl Hno.
    intros r Hb. apply check_spec_ok. rewrite openat_check, Hb. apply copyins_after_ok.
    split; [reflexivity|]. rewrite clear_copyins_eq. apply ret_only_refl.
  Qed.

  Lemma openat_ret_intro : ltac2:(tb__ "0|3|
S17Q40A1M0S1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6S83R1R2Vm;S7S1eA1M1A4A3Feff;S106Vi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M2G2S7S22A1Sb8A6Vm;G1A4A3F_;Fr;").
  Proof using Hfl Hno.
    intros. split; [eapply openat_ret_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_open_inv : ltac2:(tb__ "0|3|
S8dS1dA1S17Q40A1S1fF_;S1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6Sc2R1Vm;R2A3A3Feff;S8bVi;Vm;R3A3S3S2S7fS7fS1Sc8S7fR1Sc4A3Sa0R5S25R1A1Sb8Vm;S7S1eA1M0A5A2Le;A2S1S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3Sa0R4G2Sb8R3G2A1G0A5A2A2F_;F_;Fmk;FR;").
  Proof using Hfl Hno.
    intros R mk Hb Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite openat_check, Hb in Hs. apply copyins_after_ok in Hs as [Hci Hr].
      destruct eff as [r0 ws zs us cs ci]. rewrite clear_copyins_eq in Hr. cbn in Hci. subst ci.
      apply open_result_inv in Hr.
      destruct Hr as [(e & Hin & He & -> & ->) | (Hfree & He & -> & ->)]; inversion He; subst.
      + left. exists e. split; [exact Hin | reflexivity].
      + right. split; [exact Hfree | reflexivity].
    - exfalso. specialize (Hs probe_eff). rewrite openat_check, Hb in Hs.
      apply copyins_after_unmodeled in Hs. exact (open_result_not_unmodeled _ _ _ Hs).
  Qed.

  Lemma openat_open_intro_err_ss : ltac2:(tb__ "0|2|
S17Q40A1M0S1fF_;S7fS1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6Sc2R1Vm;R3A3A3Feff;Sc8S7fR2Sc4A3S8bVi;Vm;S8cS1dS23S25R3A1S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;Fe;Fmk;").
  Proof using Hfl Hno.
    intros mk e Hb Hin. apply check_spec_ok. rewrite openat_check, Hb. apply copyins_after_ok.
    split; [reflexivity|]. rewrite clear_copyins_eq. apply open_result_intro_err, Hin.
  Qed.

  Lemma openat_open_intro_err : ltac2:(tb__ "0|2|
S17Q40A1M0S1fF_;S7fS1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6Sc2R1Vm;R3A3A3Feff;Sc8S7fR2Sc4A3S106Vi;Vm;S8cS1dS23S25R3A1S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;Fe;Fmk;").
  Proof using Hfl Hno.
    intros. split; [eapply openat_open_intro_err_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_open_intro_ok_ss : ltac2:(tb__ "0|4|
S17Q40A1M0S1fF_;S1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6Sc2R1Vm;R2A3A3Feff;S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3S8bVi;Vm;S8cS1dS23G2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M3G3S7S22A1Sb8A6R3G2A1S7S1eA1A4A3F_;F_;Fmk;").
  Proof using Hfl Hno.
    intros mk Hb Hfree. apply check_spec_ok. rewrite openat_check, Hb. apply copyins_after_ok.
    split; [reflexivity|]. rewrite clear_copyins_eq. apply open_result_intro_ok, Hfree.
  Qed.

  Lemma openat_open_intro_ok : ltac2:(tb__ "0|4|
S17Q40A1M0S1fF_;S1dS0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R1Vm;A6Sc2R1Vm;R2A3A3Feff;S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3S106Vi;Vm;S8cS1dS23G2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M3G3S7S22A1Sb8A6R3G2A1S7S1eA1A4A3F_;F_;Fmk;").
  Proof using Hfl Hno.
    intros. split; [eapply openat_open_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_body_toolong : ltac2:(tb__ "0|0|
S1dS0S2cS2dS28Vi;A1Vpathp;A2S57A3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R2Vm;A6S83R2S25S5bA1Vm;S7S1eA1A4A3F_;Feff;").
  Proof using . intros eff Hc. unfold Open.check_openat_body. rewrite Hc. reflexivity. Qed.

  Lemma openat_toolong_inv : ltac2:(tb__ "0|0|
S8dS1dA1S0S2cS2dS28Vi;A1Vpathp;A2S57A3S8bVi;Vm;R2A3Sa0R3S25S5bA1Sb8Vm;S7S1eA1A5F_;F_;FR;").
  Proof using Hfl Hno. intros R Hc. apply openat_ret_inv. intros; apply openat_body_toolong, Hc. Qed.

  Lemma openat_toolong_intro_ss : ltac2:(tb__ "0|2|
S0S2cS2dS28Vi;A1Vpathp;A2S57A3S8bVi;Vm;S8cS1dS23S25S5bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;").
  Proof using Hfl Hno. intros Hc. apply openat_ret_intro. intros; apply openat_body_toolong, Hc. Qed.

  Lemma openat_toolong_intro : ltac2:(tb__ "0|2|
S0S2cS2dS28Vi;A1Vpathp;A2S57A3S106Vi;Vm;S8cS1dS23S25S5bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;").
  Proof using Hfl Hno.
    intros. split; [eapply openat_toolong_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_body_fault : ltac2:(tb__ "0|0|
S1dS0S2cS2dS28Vi;A1Vpathp;A2S56A3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R2Vm;A6S83R2S25S58A1Vm;S7S1eA1A4A3F_;Feff;").
  Proof using . intros eff Hc. unfold Open.check_openat_body. rewrite Hc. reflexivity. Qed.

  Lemma openat_fault_inv : ltac2:(tb__ "0|0|
S8dS1dA1S0S2cS2dS28Vi;A1Vpathp;A2S56A3S8bVi;Vm;R2A3Sa0R3S25S58A1Sb8Vm;S7S1eA1A5F_;F_;FR;").
  Proof using Hfl Hno. intros R Hc. apply openat_ret_inv. intros; apply openat_body_fault, Hc. Qed.

  Lemma openat_fault_intro_ss : ltac2:(tb__ "0|2|
S0S2cS2dS28Vi;A1Vpathp;A2S56A3S8bVi;Vm;S8cS1dS23S25S58A1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;").
  Proof using Hfl Hno. intros Hc. apply openat_ret_intro. intros; apply openat_body_fault, Hc. Qed.

  Lemma openat_fault_intro : ltac2:(tb__ "0|2|
S0S2cS2dS28Vi;A1Vpathp;A2S56A3S106Vi;Vm;S8cS1dS23S25S58A1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;").
  Proof using Hfl Hno.
    intros. split; [eapply openat_fault_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_body_empty : ltac2:(tb__ "0|0|
S1dS0S2cS2dS28Vi;A1Vpathp;A2S2fS7S17Q8A1A1A1A3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R2Vm;A6S83R2S25S45A1Vm;S7S1eA1A4A3F_;Feff;").
  Proof using . intros eff Hc. unfold Open.check_openat_body. rewrite Hc. reflexivity. Qed.

  Lemma openat_empty_inv : ltac2:(tb__ "0|0|
S8dS1dA1S0S2cS2dS28Vi;A1Vpathp;A2S2fS7S17Q8A1A1A1A3S8bVi;Vm;R2A3Sa0R3S25S45A1Sb8Vm;S7S1eA1A5F_;F_;FR;").
  Proof using Hfl Hno. intros R Hc. apply openat_ret_inv. intros; apply openat_body_empty, Hc. Qed.

  Lemma openat_empty_intro_ss : ltac2:(tb__ "0|3|
S0S2cS2dS28Vi;A1Vpathp;A2S2fS7S17Q8A1M0A1A1A3S8bVi;Vm;S8cS1dS23S25S45A1S7S8S17Q40A1M1S9G0A1A2A1S7S8G1G1A2A1M2G2S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;").
  Proof using Hfl Hno. intros Hc. apply openat_ret_intro. intros; apply openat_body_empty, Hc. Qed.

  Lemma openat_empty_intro : ltac2:(tb__ "0|3|
S0S2cS2dS28Vi;A1Vpathp;A2S2fS7S17Q8A1M0A1A1A3S106Vi;Vm;S8cS1dS23S25S45A1S7S8S17Q40A1M1S9G0A1A2A1S7S8G1G1A2A1M2G2S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;").
  Proof using Hfl Hno.
    intros. split; [eapply openat_empty_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Hypothesis Hdir : dirfd = AT_FDCWD32.

  Lemma path_eqb_cons_nil : ltac2:(tb__ "0|1|
S17Q8A1M0S9G0A1S0SaScdSbG0R2R1A3S7G0A1A2S10A3Fp;Fb;").
  Proof using . reflexivity. Qed.

  Lemma openat_body_rd : ltac2:(tb__ "0|6|
S1dS17Q8A1M0S9G0A1M1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R2R1A3A1A3S0SaSceSbG0R3R2A3A1S10A3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R5Vm;A6SaS80L_;Sc3SbG0R4R3A3M2A1Sc2R5Vm;S17Q40M3A1M4S38S47S27Vm;A1M5R1S52A3Vm;A2Lfd;A3SeG1A1S80Lx;Sc9S37Vm;A1G2A2G1Sc2R6Vm;G4S38S47G5R1S4eSbG0R6R5A3S19G3Z0A2A2A3Vm;A2Lfd;A3Ll;S83R5S25S45A1Vm;S7S1eA1A4Xex2Xax2A3F_;F_;Fp;Fb;Feff;").
  Proof using Hdir Hfl.
    intros eff b p Hc Hsl. unfold Open.check_openat_body.
    rewrite Hc, path_eqb_cons_nil, Hdir, bv_eqb_refl.
    cbn [negb]. unfold Open.check_openat_resolved. rewrite Hsl, Hfl. cbn [Z.eqb]. reflexivity.
  Qed.

  Definition openat_dir_model : Model := ltac2:(tb__ "0|1|
S38S47S27Vm;A1M0S34G0A1S52A3Vm;A2").

  Lemma path_is_dirref_cons : ltac2:(tb__ "0|2|
ScbS0SaSc3R1A1SdA3S2S17Q8A1M0G0S2S9G0A1M1G1S0ScbR4SbG0R2R1A3A3Lp;A2Lb;A2F_;Fq;").
  Proof using .
    intros q H. unfold path_is_dirref in H. destruct q as [|b p]; [cbn in H; discriminate|].
    exists b, p. reflexivity.
  Qed.

  Lemma openat_body_dirref : ltac2:(tb__ "0|0|
S1dS9S17Q8A1A1S0S2cS2dS28Vi;A1Vpathp;A2S2fR1A1A3S0SaSc3R2A1SdA3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R4Vm;A6Sc2R4Vm;S17Q40A1S38S47S27Vm;A1R1S52A3Vm;A2Lfd;A3A3F_;F_;Fq;Feff;").
  Proof using Hdir Hfl.
    intros eff q Hc Hd. destruct (path_is_dirref_cons _ Hd) as (b & p & ->).
    rewrite (openat_body_rd eff b p Hc (Open.path_is_dirref_no_slash _ Hd)), Hd. reflexivity.
  Qed.

  Lemma openat_dirref_inv : ltac2:(tb__ "0|3|
S8dS1dA1S9S17Q8A1A1S0S2cS2dS28Vi;A1Vpathp;A2S2fR1A1A3S0SaSc3R2A1SdA3S8bVi;Vm;R4A3S3S2S7fS7fS1Sc8S7fR1Sc4A3Sa0R6S25R1A1Sb8Vm;S7S1eA1M0A5A2Le;A2S1S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3Sa0R5G2Sb8Sb9G0A5A2A2F_;F_;F_;Fq;FR;").
  Proof using Hdir Hfl Hno.
    intros R q Hc Hd.
    apply (openat_open_inv R (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m)).
    intros eff. exact (openat_body_dirref eff _ Hc Hd).
  Qed.

  Lemma openat_dirref_intro_err_ss : ltac2:(tb__ "0|3|
S7fS9S17Q8A1A1M0S0S2cS2dS28Vi;A1Vpathp;A2S2fR1A1A3S0SaSc3R2A1SdA3Sc8S7fR4Sc4A3S8bVi;Vm;S8cS1dS23S25R5A1S7S8S17Q40A1M1G0A2A1S7S8G1G1A2A1M2G2S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;F_;Fq;Fe;").
  Proof using Hdir Hfl Hno.
    intros e q Hc Hd Hin.
    apply (openat_open_intro_err (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m)); [|exact Hin].
    intros eff. exact (openat_body_dirref eff _ Hc Hd).
  Qed.

  Lemma openat_dirref_intro_err : ltac2:(tb__ "0|3|
S7fS9S17Q8A1A1M0S0S2cS2dS28Vi;A1Vpathp;A2S2fR1A1A3S0SaSc3R2A1SdA3Sc8S7fR4Sc4A3S106Vi;Vm;S8cS1dS23S25R5A1S7S8S17Q40A1M1G0A2A1S7S8G1G1A2A1M2G2S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;F_;Fq;Fe;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_dirref_intro_err_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_dirref_intro_ok_ss : ltac2:(tb__ "0|5|
S9S17Q8A1A1M0S0S2cS2dS28Vi;A1Vpathp;A2S2fR1A1A3S0SaSc3R2A1SdA3S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3S8bVi;Vm;S8cS1dS23G2S7S8S17Q40A1M3G0A2A1S7S8G3G3A2A1M4G4S7S22A1Sb8A6Sb9S7S1eA1A4A3F_;F_;F_;Fq;").
  Proof using Hdir Hfl Hno.
    intros q Hc Hd Hfree.
    apply (openat_open_intro_ok (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m)); [|exact Hfree].
    intros eff. exact (openat_body_dirref eff _ Hc Hd).
  Qed.

  Lemma openat_dirref_intro_ok : ltac2:(tb__ "0|5|
S9S17Q8A1A1M0S0S2cS2dS28Vi;A1Vpathp;A2S2fR1A1A3S0SaSc3R2A1SdA3S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3S106Vi;Vm;S8cS1dS23G2S7S8S17Q40A1M3G0A2A1S7S8G3G3A2A1M4G4S7S22A1Sb8A6Sb9S7S1eA1A4A3F_;F_;F_;Fq;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_dirref_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma path_is_dirref_dot : path_is_dirref dot_path = true.
  Proof using . reflexivity. Qed.

  Lemma openat_dot_inv : ltac2:(tb__ "0|3|
S8dS1dA1S0S2cS2dS28Vi;A1Vpathp;A2S2fSf2A1A3S8bVi;Vm;R2A3S3S2S7fS7fS1Sc8S7fR1Sc4A3Sa0R4S25R1A1Sb8Vm;S7S1eA1M0A5A2Le;A2S1S0SeS24A1S2aS27Vm;A1M1S34G1A1M2A2S14S24A1A3Sa0R3G2Sb8Sb9G0A5A2A2F_;F_;FR;").
  Proof using Hdir Hfl Hno. intros R Hc. exact (openat_dirref_inv R _ Hc path_is_dirref_dot). Qed.

  Lemma openat_dot_intro_err_ss : ltac2:(tb__ "0|2|
S7fS0S2cS2dS28Vi;A1Vpathp;A2S2fSf2A1A3Sc8S7fR2Sc4A3S8bVi;Vm;S8cS1dS23S25R3A1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;Fe;").
  Proof using Hdir Hfl Hno. intros e Hc. exact (openat_dirref_intro_err e _ Hc path_is_dirref_dot). Qed.

  Lemma openat_dot_intro_err : ltac2:(tb__ "0|2|
S7fS0S2cS2dS28Vi;A1Vpathp;A2S2fSf2A1A3Sc8S7fR2Sc4A3S106Vi;Vm;S8cS1dS23S25R3A1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;Fe;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_dot_intro_err_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_dot_intro_ok_ss : ltac2:(tb__ "0|4|
S0S2cS2dS28Vi;A1Vpathp;A2S2fSf2A1A3S0SeS24A1S2aS27Vm;A1M0S34G0A1M1A2S14S24A1A3S8bVi;Vm;S8cS1dS23G1S7S8S17Q40A1M2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1Sb8A6Sb9S7S1eA1A4A3F_;F_;").
  Proof using Hdir Hfl Hno. intros Hc. exact (openat_dirref_intro_ok _ Hc path_is_dirref_dot). Qed.

  Lemma openat_dot_intro_ok : ltac2:(tb__ "0|4|
S0S2cS2dS28Vi;A1Vpathp;A2S2fSf2A1A3S0SeS24A1S2aS27Vm;A1M0S34G0A1M1A2S14S24A1A3S106Vi;Vm;S8cS1dS23G1S7S8S17Q40A1M2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1Sb8A6Sb9S7S1eA1A4A3F_;F_;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_dot_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_body_absent : ltac2:(tb__ "0|2|
S1dS17Q8A1M0S9G0A1M1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R2R1A3A1A3S0SaSc3SbG0R3R2A3A1S10A3S0SaSceSbG0R4R3A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R5R4A3A2S14G1A1A3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R7Vm;A6S83R7S25S45A1Vm;S7S1eA1A4A3F_;F_;F_;F_;Fp;Fb;Feff;").
  Proof using Hdir Hfl.
    intros eff b p Hc Hnd Hsl Hfs. rewrite (openat_body_rd eff _ _ Hc Hsl), Hnd, Hfs. reflexivity.
  Qed.

  Lemma openat_absent_inv : ltac2:(tb__ "0|2|
S8dS1dA1S17Q8A1M0S9G0A1M1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R2R1A3A1A3S0SaSc3SbG0R3R2A3A1S10A3S0SaSceSbG0R4R3A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R5R4A3A2S14G1A1A3S8bVi;Vm;R7A3Sa0R8S25S45A1Sb8Vm;S7S1eA1A5F_;F_;F_;F_;F_;Fp;Fb;FR;").
  Proof using Hdir Hfl Hno. intros R b p Hc Hnd Hsl Hfs. apply openat_ret_inv. intros; eapply openat_body_absent; eauto. Qed.

  Lemma openat_absent_intro_ss : ltac2:(tb__ "0|4|
S17Q8A1M0S9G0A1M1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R2R1A3A1A3S0SaSc3SbG0R3R2A3A1S10A3S0SaSceSbG0R4R3A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R5R4A3A2S14G1A1A3S8bVi;Vm;S8cS1dS23S25S45A1S7S8S17Q40A1M2G1A2A1S7S8G2G2A2A1M3G3S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;F_;F_;Fp;Fb;").
  Proof using Hdir Hfl Hno. intros b p Hc Hnd Hsl Hfs. apply openat_ret_intro. intros; eapply openat_body_absent; eauto. Qed.

  Lemma openat_absent_intro : ltac2:(tb__ "0|4|
S17Q8A1M0S9G0A1M1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R2R1A3A1A3S0SaSc3SbG0R3R2A3A1S10A3S0SaSceSbG0R4R3A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R5R4A3A2S14G1A1A3S106Vi;Vm;S8cS1dS23S25S45A1S7S8S17Q40A1M2G1A2A1S7S8G2G2A2A1M3G3S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;F_;F_;Fp;Fb;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_absent_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Definition openat_file_model (p : path) : Model := ltac2:(tb__ "0|1|
S38S47S27Vm;A1M0S34G0A1S4eVp;S19Q40Z0A2A2A3Vm;A2").

  Lemma openat_body_file : ltac2:(tb__ "0|3|
S1dS17Q8A1M0S9G0A1M1G1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R3R2A3A1A3S0SaSc3SbG0R4R3A3A1S10A3S0SaSceSbG0R5R4A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R6R5A3A2S12G1R4A2A3S0S80Sc1Vi;Vdirfd;Vpathp;S21Vi;U2A2R8Vm;A6Sc2R8Vm;S17Q40M2A1S38S47S27Vm;A1R1S4eSbG0R8R7A3S19G2Z0A2A2A3Vm;A2Lfd;A3A3F_;F_;F_;F_;Fdata;Fp;Fb;Feff;").
  Proof using Hdir Hfl.
    intros eff b p data Hc Hnd Hsl Hfs. rewrite (openat_body_rd eff _ _ Hc Hsl), Hnd, Hfs. reflexivity.
  Qed.

  Lemma openat_file_inv : ltac2:(tb__ "0|5|
S8dS1dA1S17Q8A1M0S9G0A1M1G1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R3R2A3A1A3S0SaSc3SbG0R4R3A3A1S10A3S0SaSceSbG0R5R4A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R6R5A3A2S12G1R4A2A3S8bVi;Vm;R8A3S3S2S7fS7fS1Sc8S7fR1Sc4A3Sa0RaS25R1A1Sb8Vm;S7S1eA1M2A5A2Le;A2S1S0SeS24A1S2aS27Vm;A1M3S34G3A1M4A2S14S24A1A3Sa0R9G4Sb8SbaSbG0R8R7A3A1G2A5A2A2F_;F_;F_;F_;F_;Fdata;Fp;Fb;FR;").
  Proof using Hdir Hfl Hno.
    intros R b p data Hc Hnd Hsl Hfs.
    apply (openat_open_inv R (fun fd => with_fds (fd_insert (m_fds m) fd (FdFile (b :: p) (Z_to_bv 64 0))) m)).
    intros eff. eapply openat_body_file; eauto.
  Qed.

  Lemma openat_file_intro_err_ss : ltac2:(tb__ "0|4|
S7fS17Q8A1M0S9G0A1M1G1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R3R2A3A1A3S0SaSc3SbG0R4R3A3A1S10A3S0SaSceSbG0R5R4A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R6R5A3A2S12G1R4A2A3Sc8S7fR8Sc4A3S8bVi;Vm;S8cS1dS23S25R9A1S7S8S17Q40A1M2G1A2A1S7S8G2G2A2A1M3G3S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;F_;F_;F_;Fdata;Fp;Fb;Fe;").
  Proof using Hdir Hfl Hno.
    intros e b p data Hc Hnd Hsl Hfs Hin.
    apply (openat_open_intro_err (fun fd => with_fds (fd_insert (m_fds m) fd (FdFile (b :: p) (Z_to_bv 64 0))) m)); [|exact Hin].
    intros eff. eapply openat_body_file; eauto.
  Qed.

  Lemma openat_file_intro_err : ltac2:(tb__ "0|4|
S7fS17Q8A1M0S9G0A1M1G1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R3R2A3A1A3S0SaSc3SbG0R4R3A3A1S10A3S0SaSceSbG0R5R4A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R6R5A3A2S12G1R4A2A3Sc8S7fR8Sc4A3S106Vi;Vm;S8cS1dS23S25R9A1S7S8S17Q40A1M2G1A2A1S7S8G2G2A2A1M3G3S7S22A1Sb8A6Vm;S7S1eA1A4A3F_;F_;F_;F_;F_;Fdata;Fp;Fb;Fe;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_file_intro_err_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma openat_file_intro_ok_ss : ltac2:(tb__ "0|6|
S17Q8A1M0S9G0A1M1G1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R3R2A3A1A3S0SaSc3SbG0R4R3A3A1S10A3S0SaSceSbG0R5R4A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R6R5A3A2S12G1R4A2A3S0SeS24A1S2aS27Vm;A1M2S34G2A1M3A2S14S24A1A3S8bVi;Vm;S8cS1dS23G3S7S8S17Q40A1M4G1A2A1S7S8G4G4A2A1M5G5S7S22A1Sb8A6SbaSbG0R8R7A3A1S7S1eA1A4A3F_;F_;F_;F_;F_;Fdata;Fp;Fb;").
  Proof using Hdir Hfl Hno.
    intros b p data Hc Hnd Hsl Hfs Hfree.
    apply (openat_open_intro_ok (fun fd => with_fds (fd_insert (m_fds m) fd (FdFile (b :: p) (Z_to_bv 64 0))) m)); [|exact Hfree].
    intros eff. eapply openat_body_file; eauto.
  Qed.

  Lemma openat_file_intro_ok : ltac2:(tb__ "0|6|
S17Q8A1M0S9G0A1M1G1S0S2cS2dS28Vi;A1Vpathp;A2S2fSbG0R3R2A3A1A3S0SaSc3SbG0R4R3A3A1S10A3S0SaSceSbG0R5R4A3A1S10A3S0SeG1A1Sc9S37Vm;A1SbG0R6R5A3A2S12G1R4A2A3S0SeS24A1S2aS27Vm;A1M2S34G2A1M3A2S14S24A1A3S106Vi;Vm;S8cS1dS23G3S7S8S17Q40A1M4G1A2A1S7S8G4G4A2A1M5G5S7S22A1Sb8A6SbaSbG0R8R7A3A1S7S1eA1A4A3F_;F_;F_;F_;F_;Fdata;Fp;Fb;").
  Proof using Hdir Hfl Hno.
    intros. split; [eapply openat_file_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End Openat.

Lemma fd32_AT_FDCWD : ltac2:(tb__ "0|3|
S17Q40M0A1M1S0S7fS93S18G0R1A2S96Z2Z20A2M2A2S97G2Z64A2A3S0G1SbbR2A1Sf3A3F_;Fw;").
Proof.
  intros w H. unfold AT_FDCWD32, fd32, abi_low32. rewrite H. reflexivity.
Qed.

Lemma openat_errno_is_error : ltac2:(tb__ "0|0|
S7fSc8S7fR1Sc4A3S0SaS5fS25R2A1A1SdA3F_;Fe;").
Proof.
  intros e Hin. pose proof (errnos_ok_range _ _ openat_errnos_ok Hin) as [H1 H2].
  apply errno_ret_error_b; assumption.
Qed.

Lemma file_read_length_le : ltac2:(tb__ "0|3|
S9S17Q8A1M0A1S17Q40M1A1M2G2S8fS90S11G0SccR3R2R1A3A2A1S18G1R1A2A2Fcount;Foff;Fdata;").
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn. unfold word_to_nat.
  pose proof (word_unsigned_range count). lia.
Qed.

Section ReadFile.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 63%Z.

  Let fd := fd32 (in_arg i 0).
  Let buf := in_arg i 1.
  Let count := in_arg i 2.

  Lemma read_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3SfdVi;Vfd;Vbuf;Vcount;R1Vm;A6A3Feff;").
  Proof using Hno. intros eff. dispatch Hno. reflexivity. Qed.

  Definition file_read_bytes (data : list byte) (off : word) : list byte :=
    file_read data off count.
  Definition read_file_model (p : path) (off : word) (bs : list byte) : Model := ltac2:(tb__ "0|0|
S38S47S27Vm;A1Vfd;S4eVp;S1bQ40Voff;Sc6S17Q8A1Vbs;A2A3A2A3Vm;A2").
  Definition read_file_eff (bs : list byte) : SyscallEffect := ltac2:(tb__ "0|2|
S23Sc6S17Q8A1Vbs;A2S103Vbuf;Vbs;A2S7S8S17Q40A1M0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6").

  Variables (p : path) (off : word) (data : list byte) (wdst : list byte).
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1Vfd;A2S12S24S4eVp;Voff;A2A2A3").
  Hypothesis Hfs : ltac2:(tb__ "0|1|
S0SeS9S17Q8A1A1M0A1Sc9S37Vm;A1Vp;A2S12G0Vdata;A2A3").

  Hypothesis Hw : ltac2:(tb__ "0|1|
S0SeS9S17Q8A1A1M0A1S49S66Vi;A1Vbuf;Vcount;A3S12G0Vwdst;A2A3").
  Hypothesis Hcnt : (bv_unsigned count <= MAX_RW_COUNT)%Z.
  Hypothesis Hok : ltac2:(tb__ "0|0|
S0SaS3eVbuf;S18Q40Vcount;A2A2SdA3").

  Lemma read_count_clamp : ltac2:(tb__ "0|1|
S0S17Q40M0A1S19G0S7bVcount;A1A2Vcount;A3").
  Proof using Hcnt.
    rewrite rw_count_clamp_small; [apply Z_to_bv_bv_unsigned|]. exact Hcnt.
  Qed.

  Lemma read_dest_prefix : ltac2:(tb__ "0|2|
S2S9S17Q8A1M0A1M1G1S0SeG1A1S49S66Vi;A1Vbuf;Sc6G0Sf8Vdata;Voff;A2A2A3S12G1R1A2A3Lw';A2").
  Proof using Hw.
    pose proof (file_read_length_le data off count) as Hle.
    pose proof (word_unsigned_range count) as Hc.
    unfold file_read_bytes.
    erewrite read_bytes_map_prefix; [eexists; reflexivity| |exact Hw].
    rewrite len_word_unsigned; [exact Hle|]. unfold buf, count in *. lia.
  Qed.

  Lemma read_file_inv : ltac2:(tb__ "0|2|
S8dS1dA1M0S8bVi;Vm;R1A3S0G0R2S8cS1dSf9Sf8Vdata;Voff;A2M1A1SfaVp;Voff;G1A3S7S1eA1A4A3F_;FR;").
  Proof using Hcnt Hfd Hfs Hno Hw Hok.
    intros R Hs. apply spec_check in Hs.
    destruct read_dest_prefix as [w' Hrb].
    unfold file_read_bytes in *.
    destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite read_check in Hs. unfold check_read in Hs. rewrite Hfd, Hok, Hfs in Hs.
      cbv zeta in Hs. cbn [negb] in Hs. rewrite read_count_clamp, Hrb in Hs.
      destruct (file_read data off count) as [|b bs] eqn:Hbs.
      + apply ret_only_inv in Hs. destruct Hs as (-> & -> & ->). reflexivity.
      + destruct eff as [r ws zs us cs ci].
        destruct ws as [|[a bs'] [|]]; try discriminate.
        destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb a buf && listN_eqb bs' (b :: bs) && bv_eqb r (len_word (b :: bs))) eqn:E;
          [|discriminate].
        apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
        apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst.
        inversion Hs; subst. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite read_check in Hs. unfold check_read in Hs.
      rewrite Hfd, Hok, Hfs in Hs. cbv zeta in Hs. cbn [negb] in Hs. rewrite read_count_clamp, Hrb in Hs.
      destruct (file_read data off count) as [|b bs].
      + exact (ret_only_not_unmodeled _ _ _ _ Hs).
      + unfold probe_eff in Hs. discriminate.
  Qed.

  Lemma read_file_intro_ss : ltac2:(tb__ "0|1|
S8bVi;Vm;S8cS1dSf9Sf8Vdata;Voff;A2M0A1SfaVp;Voff;G0A3S7S1eA1A4A3").
  Proof using Hcnt Hfd Hfs Hno Hw Hok.
    apply check_spec_ok.
    destruct read_dest_prefix as [w' Hrb].
    unfold file_read_bytes in *.
    rewrite read_check. unfold check_read. rewrite Hfd, Hok, Hfs. cbv zeta. cbn [negb].
    rewrite read_count_clamp, Hrb.
    unfold read_file_eff, read_file_model.
    destruct (file_read data off count) as [|b bs].
    - apply ret_only_refl.
    - cbn [delivered_writes]. rewrite !bv_eqb_refl.
      rewrite (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma read_file_intro : ltac2:(tb__ "0|1|
S106Vi;Vm;S8cS1dSf9Sf8Vdata;Voff;A2M0A1SfaVp;Voff;G0A3S7S1eA1A4A3").
  Proof using Hcnt Hfd Hfs Hno Hw Hok.
    intros. split; [eapply read_file_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End ReadFile.

Section ReadDir.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 63%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S52A2A3").

  Hypothesis Hok : ltac2:(tb__ "0|0|
S0SaS3eS21Vi;U1A2S18Q40S21Vi;U2A2A2A2SdA3").

  Lemma read_dir_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3S83R1S25S5aA1Vm;S7S1eA1A4A3Feff;").
  Proof using Hfd Hno Hok.
    intros eff. rewrite (read_check i m Hno). unfold check_read. rewrite Hfd, Hok. reflexivity.
  Qed.

  Lemma read_dir_inv : ltac2:(tb__ "0|0|
S8dS1dA1S8bVi;Vm;R1A3S9eR2S25S5aA1Vm;S7S1eA1A4F_;FR;").
  Proof using Hfd Hno Hok. intros R. apply check_of_ret_only. apply read_dir_check. Qed.

  Lemma read_dir_intro_ss : ltac2:(tb__ "0|2|
S8bVi;Vm;S8cS1dS23S25S5aA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3").
  Proof using Hfd Hno Hok. apply intro_ret_only. apply read_dir_check. Qed.

  Lemma read_dir_intro : ltac2:(tb__ "0|2|
S106Vi;Vm;S8cS1dS23S25S5aA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3").
  Proof using Hfd Hno Hok.
    intros. split; [eapply read_dir_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End ReadDir.

Section ReadBadf.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 63%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S14S24A1A3").

  Lemma read_badf_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3S83R1S25S3dA1Vm;S7S1eA1A4A3Feff;").
  Proof using Hfd Hno. intros eff. rewrite (read_check i m Hno). unfold check_read. rewrite Hfd. reflexivity. Qed.

  Lemma read_badf_inv : ltac2:(tb__ "0|0|
S8dS1dA1S8bVi;Vm;R1A3S9eR2S25S3dA1Vm;S7S1eA1A4F_;FR;").
  Proof using Hfd Hno. intros R. apply check_of_ret_only. apply read_badf_check. Qed.

  Lemma read_badf_intro_ss : ltac2:(tb__ "0|2|
S8bVi;Vm;S8cS1dS23S25S3dA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3").
  Proof using Hfd Hno. apply intro_ret_only. apply read_badf_check. Qed.

  Lemma read_badf_intro : ltac2:(tb__ "0|2|
S106Vi;Vm;S8cS1dS23S25S3dA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3").
  Proof using Hfd Hno.
    intros. split; [eapply read_badf_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End ReadBadf.

Lemma iovcnt32_small : ltac2:(tb__ "0|2|
S17Q40M0A1M1S92S18G0R1A2S96Z2Z20A2A2S0G1Sf5R2A1R2A3F_;Fw;").
Proof.
  intros w H. unfold iovcnt32, abi_low32.
  rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 w); lia).
  apply Z_to_bv_bv_unsigned.
Qed.

Fixpoint iovecs_at (mp : word -> option byte) (a : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, l) :: r => read_iovec_entry mp a = IovEntry b l
                   /\ (bv_unsigned l < 2 ^ 63)%Z
                   /\ iovecs_at mp (a + 16) r
  end.

Lemma copy_iovecs_aux_of : ltac2:(tb__ "0|2|
S17Q40A1M0SeS17Q8A1A1F_;S9S8G0G0A2M1A1G0Sa9R3R1R2A3S0S68S6fR4R2S11G1R3A2A3S64R3A1A3F_;Fa;Fiovs;Fmp;").
Proof.
  induction iovs as [|[b l] r IH]; intros a H; cbn; [reflexivity|].
  destruct H as (He & Hl & Hr). rewrite He. rewrite (IH _ Hr). reflexivity.
Qed.

Fixpoint iov_desc_accesses (a : word) (k : nat) : list (word * nat) :=
  match k with
  | O => []
  | S k' => (a, 16%nat) :: iov_desc_accesses (a + 16) k'
  end.

Lemma copy_iovecs_accesses_of : ltac2:(tb__ "0|3|
S17Q40A1M0SeS17Q8A1A1F_;S9S8G0G0A2M1A1G0Sa9R3R1R2A3S0S9S8G0ScA2A1S6eR4R2S11G1R3A2M2A3SafR2G2A2A3F_;Fa;Fiovs;Fmp;").
Proof.
  induction iovs as [|[b l] r IH]; intros a H; cbn; [reflexivity|].
  destruct H as (He & Hl & Hr). rewrite He. rewrite (IH _ Hr). reflexivity.
Qed.

Fixpoint iovecs_readable (mp : word -> option byte) (iovs : list (word * word)) (bs : list byte) : Prop :=
  match iovs with
  | [] => bs = []
  | (b, l) :: r => exists bs1 bs2, read_bytes_map mp b l = Some bs1
                                  /\ iovecs_readable mp r bs2 /\ bs = bs1 ++ bs2
  end.

Lemma iovecs_readable_length : ltac2:(tb__ "0|2|
S17Q40A1M0SeS17Q8A1M1A1F_;S9S8G0G0A2A1S9G1A1SaaR3R2R1A3S0S7fS90S11G1R2A2A1S60R3A1A3F_;Fbs;Fiovs;Fmp;").
Proof.
  induction iovs as [|[b l] r IH]; intros bs H; cbn in H.
  - subst. reflexivity.
  - destruct H as (bs1 & bs2 & H1 & H2 & ->). cbn [iovs_total].
    rewrite length_app, Nat2Z.inj_add, (IH _ H2), (read_bytes_map_length _ _ _ _ H1). reflexivity.
Qed.

Lemma cap_iovecs_aux_id : ltac2:(tb__ "0|2|
S9S8S17Q40A1M0G0A2A1M1S7fS8fS60R2A1R1A2S0G1S6dR3R2A2R3A3F_;Fleft;Fiovs;").
Proof.
  induction iovs as [|[b l] r IH]; intros left H; cbn [cap_iovecs_aux]; [reflexivity|].
  cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned. rewrite IH by lia. reflexivity.
Qed.

Lemma gather_prefix_of : ltac2:(tb__ "0|3|
S17Q40A1M0SeS17Q8A1M1A1F_;S9S8G0G0A2A1S9G1A1M2SaaR3R2R1A3S0G2S73R4R3A2R2A3F_;Fbs;Fiovs;Fmp;").
Proof.
  induction iovs as [|[b l] r IH]; intros bs H; cbn in H.
  - subst. reflexivity.
  - destruct H as (bs1 & bs2 & H1 & H2 & ->). cbn [gather_prefix].
    rewrite (readable_bytes_full _ _ _ _ H1).
    rewrite <- (read_bytes_map_length _ _ _ _ H1), Z.eqb_refl. rewrite (IH _ H2). reflexivity.
Qed.

Lemma access_okb_of_le : ltac2:(tb__ "0|1|
S17Q40M0A1S7fS8fZ0R1A2S8fS91S18G0R3A2R2A2S41A2S0SaS3eR4R3A2SdA3F_;F_;Fn;Fb;").
Proof.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma access_okb_le_Z : ltac2:(tb__ "0|1|
S17Q40M0A1S7fS0SaS3eR2R1A2SdA3S8fS91S18G0R3A2R2A2S41A2F_;Fn;Fb;").
Proof.
  intros b n H. unfold access_okb in H.
  apply andb_true_iff in H as [_ H]. apply Z.leb_le in H. lia.
Qed.

Lemma access_okb_mono : ltac2:(tb__ "0|0|
S17Q40A1S7fS7fS1S8fZ0R1A2S8fR1R2A2A2S0SaS3eR4R3A2SdA3S0SaS3eR5R3A2SdA3F_;F_;Fn';Fn;Fb;").
Proof.
  intros b n n' Hn H. apply access_okb_le_Z in H. apply access_okb_of_le; lia.
Qed.

Section Writev.
  Variables (i : SyscallInput) (m : Model) (ch : word).
  Variables (iovs : list (word * word)) (bs : list byte).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 66%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46Vch;A1A2A3").
  Hypothesis Hch : ch <> Z_to_bv 64 0.

  Hypothesis Hcnt : ltac2:(tb__ "0|2|
S0S7fS18Q40M0S21Vi;U2A2A2S90S11S8S17G0A1M1G1A2Viovs;A2A1A3").
  Hypothesis Hcnt1 : ltac2:(tb__ "0|2|
S1S8fZ1S90S11S8S17Q40A1M0G0A2Viovs;A2A1M1A2S8fG1S5dA2A2").
  Hypothesis Hiov : ltac2:(tb__ "0|0|
Sa9S28Vi;A1S21Vi;U1A2Viovs;A3").
  Hypothesis Hrd : ltac2:(tb__ "0|0|
SaaS28Vi;A1Viovs;Vbs;A3").

  Hypothesis Hiovok : ltac2:(tb__ "0|1|
S0SaS3eS21Vi;U1A2S99Z10S90S11S8S17Q40A1M0G0A2Viovs;A2A1A2A2SdA3").
  Hypothesis Hbok : iovs_access_okb iovs = true.

  Hypothesis Hlen : ltac2:(tb__ "0|1|
S1S8fZ1S90S11S17Q8A1Vbs;A2A1M0A2S8fG0S5eA2A2").

  Definition writev_reads (k : nat) : list (word * nat) := ltac2:(tb__ "0|1|
S15S8S17Q40A1M0ScA2SafS21Vi;U1A2S11S8G0G0A2Viovs;A2A2S76Viovs;Vk;A2A3").

  Lemma writev_iovcnt32 : ltac2:(tb__ "0|1|
S0S17Q40A1Sf5S21Vi;U2A2M0A1G0A3").
  Proof using Hcnt Hcnt1 bs. apply iovcnt32_small. unfold IOV_MAX in Hcnt1. lia. Qed.

  Lemma writev_word_to_nat : ltac2:(tb__ "0|1|
S0ScSc7S21Vi;U2A2A1S11S8S17Q40A1M0G0A2Viovs;A2A3").
  Proof using Hcnt. unfold word_to_nat. rewrite Hcnt. apply Nat2Z.id. Qed.

  Lemma writev_total : ltac2:(tb__ "0|0|
S0S7fS60Viovs;A1S90S11S17Q8A1Vbs;A2A1A3").
  Proof using Hrd. symmetry. eapply iovecs_readable_length; eauto. Qed.

  Lemma writev_cap : cap_iovecs iovs = iovs.
  Proof using Hlen Hrd.
    unfold cap_iovecs. apply cap_iovecs_aux_id. rewrite writev_total. lia.
  Qed.

  Lemma writev_not_error : ltac2:(tb__ "0|1|
ScSbeR1S11S17Q8A1M0Vbs;A2A2S0SaS5fSc6G0Sc0G0R2Vbs;A3A2A1S10A3F_;Fk;").
  Proof using Hlen iovs.
    intros k Hk. unfold addr_is_error_b. apply Z.ltb_ge.
    rewrite len_word_unsigned; rewrite length_firstn; unfold two_pow_64, MAX_RW_COUNT in *; lia.
  Qed.

  Lemma writev_import : ltac2:(tb__ "0|4|
S1S0S68S74S28Vi;A1M0S21Vi;U1A2M1Sf5S21Vi;U2A2A1M2A3S64Viovs;A1A3S0S9S8S17Q40A1M3ScA2A1S75G0G1G2A3SafG1S11S8G3G3A2Viovs;A2A2A3A2").
  Proof using Hcnt Hcnt1 Hiov Hiovok Hbok bs.
    clear Hrd Hlen. rewrite writev_iovcnt32. unfold import_iovecs, import_iovecs_accesses.
    destruct iovs as [|[b n] r] eqn:Eiovs; [cbn in Hcnt1; lia|].
    destruct r as [|[b2 n2] r2].
    -
      cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
      assert (E1 : bv_eqb (in_arg i 2) (Z_to_bv 64 1) = true).
      { apply bv_eqb_eq. apply bv_eq. rewrite Hcnt. reflexivity. }
      rewrite E1. change (16 * 1)%Z with 16%Z in Hiovok. rewrite Hiovok. cbn [negb].
      destruct Hiov as (He & Hl & _). rewrite He.
      unfold iovs_access_okb in Hbok. cbn [forallb fst snd] in Hbok. rewrite andb_true_r in Hbok.
      pose proof (bv_unsigned_in_range 64 n) as [Hn0 _].
      rewrite (access_okb_mono b (bv_unsigned n) (Z.min (bv_unsigned n) MAX_RW_COUNT)
                 ltac:(unfold MAX_RW_COUNT; lia) Hbok).
      split; reflexivity.
    -
      assert (Hc2 : (2 <= bv_unsigned (in_arg i 2))%Z) by (rewrite Hcnt; cbn [length]; lia).
      assert (E1 : bv_eqb (in_arg i 2) (Z_to_bv 64 1) = false).
      { unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
      assert (E0 : bv_eqb (in_arg i 2) (Z_to_bv 64 0) = false).
      { unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
      rewrite E1, E0.
      destruct (IOV_MAX <? bv_unsigned (in_arg i 2))%Z eqn:E2; [apply Z.ltb_lt in E2; lia|].
      rewrite Hcnt, Hiovok. cbn [negb].
      rewrite <- Eiovs in *. rewrite writev_word_to_nat.
      rewrite (copy_iovecs_aux_of _ _ _ Hiov), (copy_iovecs_accesses_of _ _ _ Hiov), Hbok.
      split; reflexivity.
  Qed.

  Lemma writev_check : ltac2:(tb__ "0|c|
S1dS0S80Sb7Vi;R1Vm;A3S1dS80Leff;R1S17Q40M0A1M1S9S8G1S9S17Q8A1M2A1A2M3A1M4S9S8G1G1A2M5A1M6G6S9S22A1M7S9S8G1ScA2A1G4S80Leff_writes;R5G6S80Leff_zeros;R4G6S80Leff_unmaps;R3G7S80Leff_copies;R2SaS80L_;M8S13S13S94Z1S18G0R6A2M9A2S94G9S90S11G2Vbs;A2A1A2A2S16S5fR6A1A1A2G8S89R1Sf4S9aG9A1MaA1A2S82Vm;SbfG2S1eS33Vch;A1Sc0G2GaVbs;A3A4A2S81Xax2S81Xax2S22G7S81Ll;Lm0;X9x2G5G6S81Ll;Lp;MbX9x2GbX9x2G3G4S81Ll;Lp;X9x2Lcopyins;Leff_copies;Leff_unmaps;Leff_zeros;Leff_writes;Lret;X1dx1A3Feff;").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hlen Hno Hrd.
    intros eff. dispatch Hno. unfold check_writev. rewrite Hfd.
    destruct (w_is0 ch) eqn:E; [apply w_is0_spec in E; contradiction|].
    destruct writev_import as [Hi1 Hi2]. rewrite Hi1, Hi2.
    cbv zeta. unfold writev_gathered. rewrite writev_cap, (gather_prefix_of _ _ _ Hrd), writev_total.
    destruct (Z.of_nat (length bs) =? 0)%Z eqn:Ez; [apply Z.eqb_eq in Ez; lia|].
    destruct (Nat.eqb (length bs) 0) eqn:En; [apply Nat.eqb_eq in En; lia|].
    pose proof (writev_not_error (length bs) ltac:(lia)) as Hne. rewrite firstn_all in Hne. rewrite Hne.
    reflexivity.
  Qed.

  Lemma writev_inv : ltac2:(tb__ "0|1|
S8dS1dA1S8bVi;Vm;R1A3S2ScScS1S1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs;A2A2A2Sa0R3S19Q40S90R1A1A2Sf4R1A1Vm;SbfG0S1eS33Vch;A1Sc0G0R1Vbs;A3A4A5A2Lk;A2F_;FR;").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hlen Hno Hrd.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite writev_check in Hs. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct us; [|discriminate]. destruct cs; [|discriminate].
      match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G; [|discriminate] end.
      match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G4; [|discriminate] end.
      apply andb_true_iff in G as [G G3]. apply andb_true_iff in G as [G1 G2].
      apply Z.leb_le in G1. apply Z.leb_le in G2. apply access_ranges_eqb_eq in G4. subst ci.
      inversion Hs; subst. exists (Z.to_nat (bv_unsigned r)). split; [lia|].
      unfold is_ret_ci. rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite writev_check in Hs. unfold probe_eff in Hs.
      cbn in Hs. discriminate.
  Qed.

  Lemma writev_intro_prefix_ss : ltac2:(tb__ "0|4|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs;A2A2A2S8bVi;Vm;S8cS1dS23S19Q40M1S90R2A1A2S7S8S17G1A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1Sf4R2A1A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2Vbs;A3A4A4A3F_;Fk;").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hlen Hno Hrd.
    intros k Hk. apply check_spec_ok. rewrite writev_check.
    assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
    { apply Z_to_bv_small. unfold bv_modulus. change (Z.of_N 64) with 64%Z. unfold MAX_RW_COUNT in Hlen. lia. }
    rewrite Hu, Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    pose proof (writev_not_error k ltac:(lia)) as Hne.
    unfold len_word in Hne. rewrite length_firstn, Nat.min_l in Hne by lia. rewrite Hne.
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma writev_intro_prefix : ltac2:(tb__ "0|4|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs;A2A2A2S106Vi;Vm;S8cS1dS23S19Q40M1S90R2A1A2S7S8S17G1A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1Sf4R2A1A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2Vbs;A3A4A4A3F_;Fk;").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hlen Hno Hrd.
    intros. split; [eapply writev_intro_prefix_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma writev_intro_ss : ltac2:(tb__ "0|3|
S8bVi;Vm;S8cS1dS23Sc6S17Q8A1M0Vbs;A2S7S8S17Q40A1M1S9G0A1A2A1S7S8G1G1A2A1M2G2S7S22A1Sf4S11G0Vbs;A2A1A6Vm;SbfG0S1eS33Vch;A1Vbs;A4A4A3").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hlen Hno Hrd.
    pose proof (writev_intro_prefix (length bs) ltac:(lia)) as H.
    rewrite firstn_all in H. exact H.
  Qed.

  Lemma writev_intro : ltac2:(tb__ "0|3|
S106Vi;Vm;S8cS1dS23Sc6S17Q8A1M0Vbs;A2S7S8S17Q40A1M1S9G0A1A2A1S7S8G1G1A2A1M2G2S7S22A1Sf4S11G0Vbs;A2A1A6Vm;SbfG0S1eS33Vch;A1Vbs;A4A4A3").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hlen Hno Hrd.
    intros. split; [eapply writev_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End Writev.

Section Writev2.
  Variables (i : SyscallInput) (m : Model) (ch : word).
  Variables (b1 l1 b2 l2 : word) (bs1 bs2 : list byte).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 66%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46Vch;A1A2A3").
  Hypothesis Hch : ch <> Z_to_bv 64 0.
  Hypothesis Hcnt : in_arg i 2 = Z_to_bv 64 2.
  Hypothesis Hv1 : ltac2:(tb__ "0|1|
S0SeS17Q40A1M0A1S6bS28Vi;A1S21Vi;U1A2A2S12G0Vb1;A2A3").

  Hypothesis Hv2 : read_u64 (in_mem i) (in_arg i 1 + 8) = Some l1.
  Hypothesis Hv3 : read_u64 (in_mem i) (in_arg i 1 + 16) = Some b2.
  Hypothesis Hv4 : read_u64 (in_mem i) (in_arg i 1 + 16 + 8) = Some l2.
  Hypothesis Hb1 : ltac2:(tb__ "0|1|
S0SeS9S17Q8A1A1M0A1S49S28Vi;A1Vb1;Vl1;A3S12G0Vbs1;A2A3").
  Hypothesis Hb2 : ltac2:(tb__ "0|1|
S0SeS9S17Q8A1A1M0A1S49S28Vi;A1Vb2;Vl2;A3S12G0Vbs2;A2A3").

  Hypothesis Hiovok : ltac2:(tb__ "0|0|
S8fS91S18Q40S21Vi;U1A2A2Z20A2S41A2").
  Hypothesis Hok1 : ltac2:(tb__ "0|1|
S8fS91S18Q40M0Vb1;A2S18G0Vl1;A2A2S41A2").
  Hypothesis Hok2 : ltac2:(tb__ "0|1|
S8fS91S18Q40M0Vb2;A2S18G0Vl2;A2A2S41A2").

  Hypothesis Hlen : ltac2:(tb__ "0|2|
S1S8fZ1S90S11S17Q8A1M0S15G0Vbs1;Vbs2;A3A2A1M1A2S8fG1S5eA2A2").

  Lemma writev2_iovecs_at : ltac2:(tb__ "0|2|
Sa9S28Vi;A1S21Vi;U1A2SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4SbG1SfG0G0Vb2;Vl2;A4S7G1A1A3A3A3").
  Proof using Hb1 Hb2 Hlen Hv1 Hv2 Hv3 Hv4.
    pose proof (read_bytes_map_length _ _ _ _ Hb1) as L1.
    pose proof (read_bytes_map_length _ _ _ _ Hb2) as L2.
    rewrite length_app, Nat2Z.inj_add in Hlen. unfold MAX_RW_COUNT in Hlen.
    cbn. unfold read_iovec_entry. rewrite Hv1, Hv2, Hv3, Hv4.
    rewrite !(proj2 (Z.leb_gt _ _)) by lia.
    repeat split; try reflexivity; lia.
  Qed.

  Lemma writev2_readable : ltac2:(tb__ "0|2|
SaaS28Vi;A1SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4SbG1SfG0G0Vb2;Vl2;A4S7G1A1A3A3S15S17Q8A1Vbs1;Vbs2;A3A3").
  Proof using Hb1 Hb2.
    cbn. exists bs1, bs2. split; [exact Hb1|]. split; [|reflexivity].
    exists bs2, []. split; [exact Hb2|]. split; [reflexivity|]. now rewrite app_nil_r.
  Qed.

  Lemma writev2_cnt : ltac2:(tb__ "0|3|
S0S7fS18Q40M0S21Vi;U2A2A2S90S11S8S17G0A1M1G1A2M2SbG2SfG1G1Vb1;Vl1;A4SbG2SfG1G1Vb2;Vl2;A4S7G2A1A3A3A2A1A3").
  Proof using Hcnt. rewrite Hcnt. reflexivity. Qed.

  Lemma writev2_cnt1 : ltac2:(tb__ "0|3|
S1S8fZ1S90S11S8S17Q40A1M0G0A2M1SbG1SfG0G0Vb1;Vl1;A4SbG1SfG0G0Vb2;Vl2;A4S7G1A1A3A3A2A1M2A2S8fG2S5dA2A2").
  Proof using bs1 bs2. cbn. unfold IOV_MAX. lia. Qed.

  Lemma writev2_iovok : ltac2:(tb__ "0|2|
S0SaS3eS21Vi;U1A2S99Z10S90S11S8S17Q40A1M0G0A2M1SbG1SfG0G0Vb1;Vl1;A4SbG1SfG0G0Vb2;Vl2;A4S7G1A1A3A3A2A1A2A2SdA3").
  Proof using Hiovok bs1 bs2. apply access_okb_of_le; cbn [length]; lia. Qed.

  Lemma writev2_bok : ltac2:(tb__ "0|2|
S0SaS69SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4SbG1SfG0G0Vb2;Vl2;A4S7G1A1A3A3A1SdA3").
  Proof using Hok1 Hok2 bs1 bs2.
    unfold iovs_access_okb. cbn [forallb fst snd].
    rewrite (access_okb_intro _ _ Hok1), (access_okb_intro _ _ Hok2). reflexivity.
  Qed.

  Definition writev2_reads (k : nat) : list (word * nat) := ltac2:(tb__ "0|2|
Sb1Vi;SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4SbG1SfG0G0Vb2;Vl2;A4S7G1A1A3A3Vk;A3").

  Lemma writev2_inv : ltac2:(tb__ "0|2|
S8dS1dA1S8bVi;Vm;R1A3S2ScScS1S1SbeU1R1A2SbeR1S11S17Q8A1M0S15G0Vbs1;Vbs2;A3M1A2A2A2Sa0R3S19Q40S90R1A1A2SfcR1A1Vm;SbfG0S1eS33Vch;A1Sc0G0R1G1A3A4A5A2Lk;A2F_;FR;").
  Proof using Hb1 Hb2 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hv3 Hv4 Hiovok Hok1 Hok2.
    intros R. eapply writev_inv; eauto using writev2_iovecs_at, writev2_readable, writev2_cnt, writev2_cnt1,
      writev2_iovok, writev2_bok.
  Qed.

  Lemma writev2_intro_prefix_ss : ltac2:(tb__ "0|5|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0S15G0Vbs1;Vbs2;A3M1A2A2A2S8bVi;Vm;S8cS1dS23S19Q40M2S90R2A1A2S7S8S17G2A1M3S9G0A1A2A1S7S8G3G3A2A1M4G4S7S22A1SfcR2A1A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2G1A3A4A4A3F_;Fk;").
  Proof using Hb1 Hb2 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hv3 Hv4 Hiovok Hok1 Hok2.
    intros k Hk. eapply writev_intro_prefix; eauto using writev2_iovecs_at, writev2_readable, writev2_cnt,
      writev2_cnt1, writev2_iovok, writev2_bok.
  Qed.

  Lemma writev2_intro_prefix : ltac2:(tb__ "0|5|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0S15G0Vbs1;Vbs2;A3M1A2A2A2S106Vi;Vm;S8cS1dS23S19Q40M2S90R2A1A2S7S8S17G2A1M3S9G0A1A2A1S7S8G3G3A2A1M4G4S7S22A1SfcR2A1A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2G1A3A4A4A3F_;Fk;").
  Proof using Hb1 Hb2 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hv3 Hv4 Hiovok Hok1 Hok2.
    intros. split; [eapply writev2_intro_prefix_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma writev2_intro_ss : ltac2:(tb__ "0|4|
S8bVi;Vm;S8cS1dS23Sc6S17Q8A1M0S15G0Vbs1;Vbs2;A3M1A2S7S8S17Q40A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1SfcS11G0G1A2A1A6Vm;SbfG0S1eS33Vch;A1G1A4A4A3").
  Proof using Hb1 Hb2 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hv3 Hv4 Hiovok Hok1 Hok2.
    eapply writev_intro; eauto using writev2_iovecs_at, writev2_readable, writev2_cnt, writev2_cnt1,
      writev2_iovok, writev2_bok.
  Qed.

  Lemma writev2_intro : ltac2:(tb__ "0|4|
S106Vi;Vm;S8cS1dS23Sc6S17Q8A1M0S15G0Vbs1;Vbs2;A3M1A2S7S8S17Q40A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1SfcS11G0G1A2A1A6Vm;SbfG0S1eS33Vch;A1G1A4A4A3").
  Proof using Hb1 Hb2 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hv3 Hv4 Hiovok Hok1 Hok2.
    intros. split; [eapply writev2_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma writev2_ret : ltac2:(tb__ "0|2|
S0S7fS18Q40M0Sc6S17Q8A1M1S15G1Vbs1;Vbs2;A3A2A2S91S18G0Vl1;A2S18G0Vl2;A2A2A3").
  Proof using Hb1 Hb2 Hlen.
    rewrite len_word_unsigned; [|unfold two_pow_64, MAX_RW_COUNT in *; lia].
    rewrite length_app, Nat2Z.inj_add.
    rewrite (read_bytes_map_length _ _ _ _ Hb1), (read_bytes_map_length _ _ _ _ Hb2). reflexivity.
  Qed.
End Writev2.

Section Writev1.
  Variables (i : SyscallInput) (m : Model) (ch : word).
  Variables (b1 l1 : word) (bs1 : list byte).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 66%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SeS24A1S2aS27Vm;A1SbbS21Vi;U0A2A1A2S12S24S46Vch;A1A2A3").
  Hypothesis Hch : ch <> Z_to_bv 64 0.
  Hypothesis Hcnt : in_arg i 2 = Z_to_bv 64 1.
  Hypothesis Hv1 : ltac2:(tb__ "0|1|
S0SeS17Q40A1M0A1S6bS28Vi;A1S21Vi;U1A2A2S12G0Vb1;A2A3").
  Hypothesis Hv2 : read_u64 (in_mem i) (in_arg i 1 + 8) = Some l1.
  Hypothesis Hb1 : ltac2:(tb__ "0|1|
S0SeS9S17Q8A1A1M0A1S49S28Vi;A1Vb1;Vl1;A3S12G0Vbs1;A2A3").

  Hypothesis Hiovok : ltac2:(tb__ "0|0|
S8fS91S18Q40S21Vi;U1A2A2Z10A2S41A2").
  Hypothesis Hok1 : ltac2:(tb__ "0|1|
S8fS91S18Q40M0Vb1;A2S18G0Vl1;A2A2S41A2").

  Hypothesis Hlen : ltac2:(tb__ "0|1|
S1S8fZ1S90S11S17Q8A1Vbs1;A2A1M0A2S8fG0S5eA2A2").

  Lemma writev1_iovecs_at : ltac2:(tb__ "0|2|
Sa9S28Vi;A1S21Vi;U1A2SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4S7G1A1A3A3").
  Proof using Hb1 Hlen Hv1 Hv2.
    pose proof (read_bytes_map_length _ _ _ _ Hb1) as L1. unfold MAX_RW_COUNT in Hlen.
    cbn. unfold read_iovec_entry. rewrite Hv1, Hv2.
    rewrite !(proj2 (Z.leb_gt _ _)) by lia.
    repeat split; try reflexivity; lia.
  Qed.

  Lemma writev1_readable : ltac2:(tb__ "0|2|
SaaS28Vi;A1SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4S7G1A1A3Vbs1;A3").
  Proof using Hb1.
    cbn. exists bs1, []. split; [exact Hb1|]. split; [reflexivity|]. now rewrite app_nil_r.
  Qed.

  Lemma writev1_cnt : ltac2:(tb__ "0|3|
S0S7fS18Q40M0S21Vi;U2A2A2S90S11S8S17G0A1M1G1A2M2SbG2SfG1G1Vb1;Vl1;A4S7G2A1A3A2A1A3").
  Proof using Hcnt. rewrite Hcnt. reflexivity. Qed.

  Lemma writev1_cnt1 : ltac2:(tb__ "0|3|
S1S8fZ1S90S11S8S17Q40A1M0G0A2M1SbG1SfG0G0Vb1;Vl1;A4S7G1A1A3A2A1M2A2S8fG2S5dA2A2").
  Proof using bs1. cbn. unfold IOV_MAX. lia. Qed.

  Lemma writev1_iovok : ltac2:(tb__ "0|2|
S0SaS3eS21Vi;U1A2S99Z10S90S11S8S17Q40A1M0G0A2M1SbG1SfG0G0Vb1;Vl1;A4S7G1A1A3A2A1A2A2SdA3").
  Proof using Hiovok bs1. apply access_okb_of_le; cbn [length]; lia. Qed.

  Lemma writev1_bok : ltac2:(tb__ "0|2|
S0SaS69SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4S7G1A1A3A1SdA3").
  Proof using Hok1 bs1.
    unfold iovs_access_okb. cbn [forallb fst snd].
    rewrite (access_okb_intro _ _ Hok1). reflexivity.
  Qed.

  Definition writev1_reads (k : nat) : list (word * nat) := ltac2:(tb__ "0|2|
Sb1Vi;SbS8S17Q40A1M0G0A2M1SfG0G0Vb1;Vl1;A4S7G1A1A3Vk;A3").

  Lemma writev1_inv : ltac2:(tb__ "0|1|
S8dS1dA1S8bVi;Vm;R1A3S2ScScS1S1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs1;A2A2A2Sa0R3S19Q40S90R1A1A2SfbR1A1Vm;SbfG0S1eS33Vch;A1Sc0G0R1Vbs1;A3A4A5A2Lk;A2F_;FR;").
  Proof using Hb1 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hiovok Hok1.
    intros R. eapply writev_inv; eauto using writev1_iovecs_at, writev1_readable, writev1_cnt, writev1_cnt1,
      writev1_iovok, writev1_bok.
  Qed.

  Lemma writev1_intro_prefix_ss : ltac2:(tb__ "0|4|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs1;A2A2A2S8bVi;Vm;S8cS1dS23S19Q40M1S90R2A1A2S7S8S17G1A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1SfbR2A1A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2Vbs1;A3A4A4A3F_;Fk;").
  Proof using Hb1 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hiovok Hok1.
    intros k Hk. eapply writev_intro_prefix; eauto using writev1_iovecs_at, writev1_readable, writev1_cnt,
      writev1_cnt1, writev1_iovok, writev1_bok.
  Qed.

  Lemma writev1_intro_prefix : ltac2:(tb__ "0|4|
ScS1SbeU1R1A2SbeR1S11S17Q8A1M0Vbs1;A2A2A2S106Vi;Vm;S8cS1dS23S19Q40M1S90R2A1A2S7S8S17G1A1M2S9G0A1A2A1S7S8G2G2A2A1M3G3S7S22A1SfbR2A1A6Vm;SbfG0S1eS33Vch;A1Sc0G0R2Vbs1;A3A4A4A3F_;Fk;").
  Proof using Hb1 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hiovok Hok1.
    intros. split; [eapply writev1_intro_prefix_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma writev1_intro_ss : ltac2:(tb__ "0|3|
S8bVi;Vm;S8cS1dS23Sc6S17Q8A1M0Vbs1;A2S7S8S17Q40A1M1S9G0A1A2A1S7S8G1G1A2A1M2G2S7S22A1SfbS11G0Vbs1;A2A1A6Vm;SbfG0S1eS33Vch;A1Vbs1;A4A4A3").
  Proof using Hb1 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hiovok Hok1.
    eapply writev_intro; eauto using writev1_iovecs_at, writev1_readable, writev1_cnt, writev1_cnt1,
      writev1_iovok, writev1_bok.
  Qed.

  Lemma writev1_intro : ltac2:(tb__ "0|3|
S106Vi;Vm;S8cS1dS23Sc6S17Q8A1M0Vbs1;A2S7S8S17Q40A1M1S9G0A1A2A1S7S8G1G1A2A1M2G2S7S22A1SfbS11G0Vbs1;A2A1A6Vm;SbfG0S1eS33Vch;A1Vbs1;A4A4A3").
  Proof using Hb1 Hch Hcnt Hfd Hlen Hno Hv1 Hv2 Hiovok Hok1.
    intros. split; [eapply writev1_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End Writev1.

Definition mmap_nZ (len : word) : Z := page_round_up_Z (bv_unsigned len).
Definition mmap_n (len : word) : word := Z_to_bv 64 (mmap_nZ len).

Definition alloc_ceiling_lo : Z := 0x7fff7f800000.
Definition alloc_ceiling_hi : Z := 0x7fffff800000.

Definition init_sp_ok (h : VmMaps) : Prop := ltac2:(tb__ "0|1|
S1S8fS63S18Q40S26Vh;A1A2M0A2S8fG0S62A2A2").

Lemma alloc_ceiling_lo_val : ltac2:(tb__ "0|0|
S0S7fSaeS97S63S6cA2A3").
Proof. reflexivity. Qed.
Lemma alloc_ceiling_hi_val : ltac2:(tb__ "0|0|
S0S7fSadS97S62S6cA2A3").
Proof. reflexivity. Qed.

Lemma alloc_top_bounds : ltac2:(tb__ "0|1|
S29S9dR1A1S1S8fSaeS35R2A1M0A2S8fG0SadA2A2F_;Fh;").
Proof.
  intros h [H1 H2]. unfold alloc_top, alloc_ceiling_lo, alloc_ceiling_hi.
  unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.

Lemma alloc_top_ge_lo : ltac2:(tb__ "0|0|
S29S7fS9dR2A1S8fR2SaeA2S8fR3S35R4A1A2F_;F_;Fz;Fh;").
Proof. intros h z H Hz. pose proof (alloc_top_bounds h H). lia. Qed.

Lemma alloc_top_le_hi : ltac2:(tb__ "0|0|
S29S7fS9dR2A1S8fR2S35R3A1A2S8fR3SadA2F_;F_;Fz;Fh;").
Proof. intros h z H Hz. pose proof (alloc_top_bounds h H). lia. Qed.

Lemma alloc_ceiling_hi_lt : (alloc_ceiling_hi < two_pow_64 - 4096)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma alloc_top_lt : ltac2:(tb__ "0|0|
S29S92S35R1A1S97S53Z1000A2A2Fh;").
Proof. intros h. pose proof (alloc_top_room h). unfold stack_max_size in *. lia. Qed.

Lemma init_sp_ok_init_model : ltac2:(tb__ "0|2|
S9S8S17Q40M0A1M1G1A2A1G1G1G1S7fS65S8fS63S18G0R3A2A2S8fS18G0R4A2S62A2S9dS20S67R8R7R6R5R4R3A6A1A1F_;F_;Finp;Flim;Fsp;Fmbase;Fbrk0;Freserved;").
Proof. intros reserved brk0 mbase sp lim inp H1 H2. unfold init_sp_ok. rewrite m_vmmaps_init_model. cbn. lia. Qed.

Lemma vm_init_sp_init_model : ltac2:(tb__ "0|1|
S9S8S17Q40A1M0G0A2A1G0G0G0S7fS65S0G0S26S20S67R6R5R4R3R2R1A6A1A1R3A3Finp;Flim;Fsp;Fmbase;Fbrk0;Freserved;").
Proof. reflexivity. Qed.

Lemma init_sp_ok_same : ltac2:(tb__ "0|1|
S29S29S0S17Q40A1S26R1A1S26R2A1A3S9dR3A1M0G0F_;F_;Fh';Fh;").
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Lemma alloc_top_same : ltac2:(tb__ "0|0|
S29S29S0S17Q40A1S26R1A1S26R2A1A3S0S7fS35R2A1S35R3A1A3F_;Fh';Fh;").
Proof. intros h h' E. unfold alloc_top. rewrite E. reflexivity. Qed.

Lemma vm_init_sp_mkVmMapsFull : ltac2:(tb__ "0|2|
S9S8S17Q40A1M0G0A2A1M1G1G1G0G0S7fG0G0S0G0S26S43R8R7R6R5R4R3R2R1A8A1R1A3Fisp;Fmb;Fl;Fb;Fsb;Fna;Fms;Fr;").
Proof. reflexivity. Qed.

Lemma m_vmmaps_with_fds : ltac2:(tb__ "0|0|
S9S8S17Q40A1S24A2A1S1fS0S29S20S38R2R1A2A1S20R1A1A3Fm;Ff;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_stdin : ltac2:(tb__ "0|0|
S4fS1fS0S29S20S55R2R1A2A1S20R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_fs' : ltac2:(tb__ "0|0|
ScaS1fS0S29S20S54R2R1A2A1S20R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_halted : ltac2:(tb__ "0|0|
S17Q40A1S1fS0S29S20S51R2R1A2A1S20R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_tid : ltac2:(tb__ "0|0|
S17Q40A1S1fS0S29S20S4dR2R1A2A1S20R1A1A3Fm;Fv;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_vmmaps' : ltac2:(tb__ "0|0|
S29S1fS0S29S20S3cR2R1A2A1R2A3Fm;Fh;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_vm_backing : ltac2:(tb__ "0|1|
S9S8S17Q40A1M0G0A2A1S9G0A1S1fS0S29S20S7eR3R2R1A3A1S20R1A1A3Fm;Fmt;Flz;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_add_lazy : ltac2:(tb__ "0|1|
S17Q40A1M0G0S1fS0S29S20S7cR3R2R1A3A1S20R1A1A3Fm;Fn;Fa;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing : ltac2:(tb__ "0|1|
S17Q40A1M0G0G0S1fS0S29S20SdcR4R3R2R1A4A1S20R1A1A3Fm;Fn;Fa;Fflags;").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Definition mmap_place_ok (addr flags : word) (m : Model) (len a : word) : Prop := ltac2:(tb__ "0|6|
S1S0S7fS93S18Q40M0Va;A2M1S32A2Z0M2A3S1S92G2G1A2S1S8fS91G1S9fVlen;A1M3A2S35S20Vm;A1M4A1A2S1S0SaS3fS15S8S17G0A1M5G5A2S36G4A1S2eG4A1A3Va;Sa1Vlen;A1A3SdA3S0SaSdaVflags;Vm;G3A3SdA3A2A2A2A2").

Definition mmap_place_ok_none (addr : word) (m : Model) (len a : word) : Prop := ltac2:(tb__ "0|5|
S1S0S7fS93S18Q40M0Va;A2M1S32A2Z0M2A3S1S92G2G1A2S1S8fS91G1S9fVlen;A1A2S35S20Vm;A1M3A1A2S0SaS3fS15S8S17G0A1M4G4A2S36G3A1S2eG3A1A3Va;Sa1Vlen;A1A3SdA3A2A2A2").

Definition mmap_rw_vm (h : VmMaps) (len a : word) : VmMaps := ltac2:(tb__ "0|1|
S43S36Vh;A1SbS8S17Q40A1M0G0A2SfG0G0Va;Sa1Vlen;A1A4S2eVh;A1A3S39Vh;A1S3aVh;A1S2bVh;A1S44Vh;A1S4aVh;A1S26Vh;A1A8").
Definition mmap_none_vm (h : VmMaps) (len a : word) : VmMaps := ltac2:(tb__ "0|3|
S43S36Vh;A1SbS8S17Q40A1M0G0A2M1SfG0G0Va;Sa1Vlen;A1A4M2S2eVh;A1A3SbG1G2S39Vh;A1A3S3aVh;A1S2bVh;A1S44Vh;A1S4aVh;A1S26Vh;A1A8").

Definition mmap_rw_model (flags : word) (m : Model) (len a : word) : Model := ltac2:(tb__ "0|0|
SdcVflags;Va;Sa1Vlen;A1S3cSb5S20Vm;A1Vlen;Va;A3Vm;A2A4").
Definition mmap_none_model (flags : word) (m : Model) (len a : word) : Model := ltac2:(tb__ "0|0|
SdcVflags;Va;Sa1Vlen;A1S3cSb4S20Vm;A1Vlen;Va;A3Vm;A2A4").

Lemma vm_init_sp_mmap_rw_model : ltac2:(tb__ "0|1|
S17Q40A1M0S1fG0G0S0G0S26S20Sa4R4R3R2R1A4A1A1S26S20R3A1A1A3Fa;Flen;Fm;Fflags;").
Proof. intros. unfold mmap_rw_model. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.
Lemma vm_init_sp_mmap_none_model : ltac2:(tb__ "0|1|
S17Q40A1M0S1fG0G0S0G0S26S20Sa3R4R3R2R1A4A1A1S26S20R3A1A1A3Fa;Flen;Fm;Fflags;").
Proof. intros. unfold mmap_none_model. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.

Lemma mmap_flags_core_34 : ltac2:(tb__ "0|2|
S17Q40M0A1S0S7fS18G0R1A2Z22M1A3S0S7fSd8R2A1G1A3F_;Fflags;").
Proof. intros flags H. unfold mmap_flags_core. rewrite H. reflexivity. Qed.

Lemma mmap_flags_core_50 : ltac2:(tb__ "0|2|
S17Q40M0A1S0S7fS18G0R1A2Z32M1A3S0S7fSd8R2A1G1A3F_;Fflags;").
Proof. intros flags H. unfold mmap_flags_core. rewrite H. reflexivity. Qed.

Lemma mmap_noreserve_b_34 : ltac2:(tb__ "0|1|
S17Q40M0A1S0S7fS18G0R1A2Z22A3S0SaSd9R2A1S10A3F_;Fflags;").
Proof. intros flags H. unfold mmap_noreserve_b. rewrite H. reflexivity. Qed.

Lemma mmap_noreserve_b_50 : ltac2:(tb__ "0|1|
S17Q40M0A1S0S7fS18G0R1A2Z32A3S0SaSd9R2A1S10A3F_;Fflags;").
Proof. intros flags H. unfold mmap_noreserve_b. rewrite H. reflexivity. Qed.

Lemma with_mmap_backing_plain : ltac2:(tb__ "0|1|
S17Q40A1M0G0G0S1fS0SaSd9R4A1S10A3S0S1fSdcR5R4R3R2A4R2A3F_;Fm;Fn;Fa;Fflags;").
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.

Lemma mmap_noreserve_backed_ok_plain : ltac2:(tb__ "0|0|
S17Q40A1S1fS7fS0SaSd9R3A1S10A3S0SaSdaR4R3R2A3S94S91S7dR3A1R2A2S44S20R3A1A1A2A3F_;FnZ;Fm;Fflags;").
Proof. intros flags m nZ H. unfold mmap_noreserve_backed_ok. rewrite H. reflexivity. Qed.

Lemma mmap_anon_b_of_core : ltac2:(tb__ "0|0|
S17Q40A1S0SaS9bSd8R1A1Z5A2SdA3S0SaSd1R2A1SdA3F_;Fflags;").
Proof.
  intros flags H. unfold mmap_flags_core in H. rewrite Z.ldiff_spec in H.
  apply andb_true_iff in H as [H _].
  unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intros E.
  assert (H0 : Z.testbit (Z.land (bv_unsigned flags) MAP_ANONYMOUS) 5 = false) by (rewrite E; reflexivity).
  rewrite Z.land_spec, H in H0. cbn in H0. discriminate.
Qed.

Lemma mmap_off_aligned_b_of_is0 : ltac2:(tb__ "0|0|
S17Q40A1S0SaSbcR1A1SdA3S0SaSd4R2A1SdA3F_;Foff;").
Proof. intros off H. apply w_is0_spec in H. subst. reflexivity. Qed.

Lemma mmap_shape_gates : ltac2:(tb__ "0|1|
S17Q40A1M0G0S7fS0SaS13S95Sd8R3A1R1A2SbcR2A1A2SdA3S0SaS9bR2Z5A2SdA3S1S0SaSd4R4A1SdA3S0SaSd1R5A1SdA3A2F_;F_;Fc;Foff;Fflags;").
Proof.
  intros flags off c H Hc. apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1.
  split; [apply mmap_off_aligned_b_of_is0, H2 | apply mmap_anon_b_of_core; rewrite H1; exact Hc].
Qed.

Lemma mmap_modeled_b_gates : ltac2:(tb__ "0|1|
S17Q40A1M0G0G0S0SaScfR3R2R1A3SdA3S1S0SaSd4R2A1SdA3S0SaSd1R3A1SdA3A2F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off H. unfold mmap_modeled_b in H. rewrite <- andb_assoc in H.
  apply andb_true_iff in H as [_ H]. eapply mmap_shape_gates; [exact H | reflexivity].
Qed.

Lemma mmap_noaccess_b_gates : ltac2:(tb__ "0|1|
S17Q40A1M0G0G0S0SaSd3R3R2R1A3SdA3S1S0SaSd4R2A1SdA3S0SaSd1R3A1SdA3A2F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off H. unfold mmap_noaccess_b in H. rewrite <- andb_assoc in H.
  apply andb_true_iff in H as [_ H]. eapply mmap_shape_gates; [exact H | reflexivity].
Qed.

Lemma mmap_fixed_noaccess_b_gates : ltac2:(tb__ "0|1|
S17Q40A1M0G0G0S0SaSe0R3R2R1A3SdA3S1S0SaSd4R2A1SdA3S0SaSd1R3A1SdA3A2F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off H. unfold mmap_fixed_noaccess_b in H. rewrite <- andb_assoc in H.
  apply andb_true_iff in H as [_ H]. eapply mmap_shape_gates; [exact H | reflexivity].
Qed.

Lemma mmap_modeled_b_intro : ltac2:(tb__ "0|3|
S17Q40M0A1M1G1G1S0S7fS18G0R3A2M2Z3A3S0S7fG2Z22A3S0G1R3S19G0Z0A2A3S0SaScfR6R5R4A3SdA3F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->. unfold mmap_modeled_b.
  rewrite Hp, (mmap_flags_core_34 _ Hf). reflexivity.
Qed.

Lemma mmap_noaccess_b_intro : ltac2:(tb__ "0|4|
S17Q40M0A1M1G1G1S0S7fS18G0R3A2M2Z0M3A3S0S7fG2Z22A3S0G1R3S19G0G3A2A3S1S0SaSd3R6R5R4A3SdA3S0SaScfR6R5R4A3S10A3A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->. unfold mmap_noaccess_b, mmap_modeled_b.
  rewrite Hp, (mmap_flags_core_34 _ Hf). split; reflexivity.
Qed.

Lemma mmap_fixed_noaccess_b_intro : ltac2:(tb__ "0|4|
S17Q40M0A1M1G1G1S0S7fS18G0R3A2M2Z0M3A3S0S7fG2Z32A3S0G1R3S19G0G3A2A3S1S0SaSe0R6R5R4A3SdA3S1S0SaSd3R6R5R4A3S10A3S0SaScfR6R5R4A3S10A3A2A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->.
  unfold mmap_fixed_noaccess_b, mmap_noaccess_b, mmap_modeled_b.
  rewrite Hp, (mmap_flags_core_50 _ Hf). repeat split; reflexivity.
Qed.

Lemma mmap_fd_none_of_unsigned : ltac2:(tb__ "0|2|
S17Q40M0A1M1S0S7fS18G0R1A2S97S96Z2Z40A2Z1A2A3S0G1R2Se8A3F_;Ffd;").
Proof. intros fd H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma mmap_errnos_ok : errnos_ok mmap_errnos = true.
Proof. reflexivity. Qed.

Lemma mmap_place_not_errno : ltac2:(tb__ "0|1|
S29S17Q40M0A1S7fS8fZ0R1A2S8fS91S18G0R3A2R2A2S35R4A1A2S0SaS85Se7R4A2S10A3F_;F_;FnZ;Fa;Fh;").
Proof.
  intros h a nZ Hn Hc. apply errno_ret_in_below; [reflexivity|].
  pose proof (alloc_top_lt h). lia.
Qed.

Lemma mmap_nZ_nonneg : ltac2:(tb__ "0|0|
S17Q40A1S8fZ0S9fR1A1A2Flen;").
Proof.
  intros len. unfold mmap_nZ. pose proof (word_unsigned_range len).
  apply page_round_up_Z_nonneg. lia.
Qed.

Lemma mmap_place_okb : ltac2:(tb__ "0|6|
S17Q40M0A1M1G1S1fG1G1S4Sa7R5R4R3R2R1A5S0SaS13S13S13S13S95S93S18G0R1A2M2S32A2Z0M3A2S98G3G2A2A2S94S91G2S9fR2A1M4A2S35S20R3A1M5A1A2A2S3fS15S8G1G1A2S36G5A1S2eG5A1A3R1Sa1R2A1A3A2SdaR4R3G4A3A2SdA3A2Fa;Flen;Fm;Fflags;Faddr;").
Proof.
  intros addr flags m len a. unfold mmap_place_ok.
  rewrite !andb_true_iff, Z.eqb_eq, Z.ltb_lt, !Z.leb_le. tauto.
Qed.

Lemma mmap_place_ok_noneb : ltac2:(tb__ "0|5|
S17Q40M0A1M1S1fG1G1S4Sa8R4R3R2R1A4S0SaS13S13S13S95S93S18G0R1A2M2S32A2Z0M3A2S98G3G2A2A2S94S91G2S9fR2A1A2S35S20R3A1M4A1A2A2S3fS15S8G1G1A2S36G4A1S2eG4A1A3R1Sa1R2A1A3A2SdA3A2Fa;Flen;Fm;Faddr;").
Proof.
  intros addr m len a. unfold mmap_place_ok_none.
  rewrite !andb_true_iff, Z.eqb_eq, Z.ltb_lt, !Z.leb_le. tauto.
Qed.

Section MmapRW.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Hypothesis Hlen : len <> Z_to_bv 64 0.

  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0SaScfS21Vi;U2A2S21Vi;U3A2S21Vi;U5A2A3SdA3").

  Lemma mmap_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3S100S21Vi;U0A2Vlen;S21Vi;U2A2S21Vi;U3A2S21Vi;U4A2S21Vi;U5A2R1Vm;A8A3Feff;").
  Proof using Hno. intros eff. dispatch Hno. reflexivity. Qed.

  Lemma mmap_len_gate : w_is0 len = false.
  Proof using Hlen. destruct (w_is0 len) eqn:E; [apply w_is0_spec in E; contradiction|reflexivity]. Qed.

  Lemma mmap_rw_reduce : ltac2:(tb__ "0|11|
S1dS0S80Sb7Vi;R1Vm;A3S1dS80Leff;R1S17Q40M0A1M1S9S8G1S9S17Q8A1A1A2M2A1M3S9S8G1G1A2M4A1M5G5S9S22A1M6S9S8G1ScA2M7A1M8G3S80Leff_writes;R5G5S80Leff_unmaps;R3G6S80Leff_copies;R2G8S80Leff_copyins;R1SaS80L_;M9S85SdfSd2Vflags;Vm;S9fVlen;A1MaA3A1R6A2G5S80Lzs;R4S82Vm;S7S1eA1MbA2G4G5S81Ll;Lp;McX9x2G9S13S13S13S13S13S95S93S18G0R6A2MdS32A2Z0MeA2S98GeGdA2A2S94S91GdGaA2S35S20Vm;A1MfA1A2A2S3fS15G4S36GfA1S2eGfA1A3R6Sa1Vlen;A1M10A3A2SdaVflags;Vm;GaA3A2S86R4SbG4SfG1G1R6G10A4S7G4A1A3A2A2S82Sa4Vflags;Vm;Vlen;R6A4GbA2S81Xax2Xax2G7G8S81Ll;Lp;X9x2S22G6S81Ll;Lm0;X9x2GcX9x2G2G3S81Ll;Lp;X9x2Leff_copyins;Leff_copies;Leff_unmaps;Lzs;Leff_writes;Lr;X1dx1A3Feff;").
  Proof using Hlen Hno Hshape.
    intros eff. rewrite mmap_check. unfold check_mmap.
    destruct (mmap_modeled_b_gates _ _ _ Hshape) as [G1 G2]. rewrite G1, G2, mmap_len_gate, Hshape.
    reflexivity.
  Qed.

  Lemma mmap_rw_inv : ltac2:(tb__ "0|5|
S8dS1dA1M0S8bVi;Vm;R1A3S3S9eR2S25S3bA1Vm;S7S1eA1M1A4S2S17Q40A1M2G2S1Sa7Vaddr;Vflags;Vm;Vlen;R1A5S0G0R3S8cS1dS23R1S7S8G2S9S17Q8A1A1A2A1SbS8G2G2A2M3SfG2G2R1Sa1Vlen;A1A4S7G3A1M4A3G4S7S22A1S7S8G2ScA2A1A6Sa4Vflags;Vm;Vlen;R1A4G1A4A3A2La;A2A2F_;FR;").
  Proof using Hlen Hno Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_rw_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in (mmap_errnos_when (mmap_grant_refusable flags m (mmap_nZ len))) r) eqn:E.
      + destruct zs; [|discriminate].
        unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->).
        destruct Hin as [<-|[]]. inversion Hs; subst. left. reflexivity.
      + right. exists r.
        match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G; [|discriminate] end.
        apply andb_true_iff in G as [G Gz]. apply listNN_eqb_eq in Gz. subst zs.
        inversion Hs; subst. split; [|reflexivity].
        apply mmap_place_okb. exact G.
    - exfalso. specialize (Hs probe_eff). rewrite mmap_rw_reduce in Hs. unfold probe_eff in Hs.
      destruct (errno_ret_in _ (Z_to_bv 64 0)); [discriminate|].
      match type of Hs with (if ?c then _ else _) = _ => destruct c; discriminate end.
  Qed.

  Lemma mmap_rw_intro_fail_ss : ltac2:(tb__ "0|2|
S0SaSd2Vflags;Vm;S9fVlen;A1A3SdA3S8bVi;Vm;S8cS1dS23S25S3bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hlen Hno Hshape.
    intros Hrf. apply check_spec_ok. rewrite mmap_rw_reduce. rewrite Hrf. unfold mmap_errnos_when.
    rewrite (errno_ret_in_intro mmap_errnos ENOMEM ltac:(left; reflexivity)). reflexivity.
  Qed.

  Lemma mmap_rw_intro_fail : ltac2:(tb__ "0|2|
S0SaSd2Vflags;Vm;S9fVlen;A1A3SdA3S106Vi;Vm;S8cS1dS23S25S3bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hlen Hno Hshape.
    intros. split; [eapply mmap_rw_intro_fail_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_forced_mmap; [assumption|]. intros ? ? ? Hs'. destruct (mmap_rw_inv _ Hs') as [He | (a & (Hal & Hpos & Htop & Hfree & Hb) & E')]; [unfold is_ret in He; inversion He; subst; reflexivity | exfalso; unfold mmap_n in Hfree; match goal with F : mmap_grant_refusable _ _ _ = true |- _ => rewrite (grant_not_refusable_of _ _ _ _ Hal Hpos Htop Hfree Hb) in F; discriminate F end].
  Qed.

  Lemma mmap_rw_intro_ok_ss : ltac2:(tb__ "0|3|
S17Q40A1M0Sa7Vaddr;Vflags;Vm;Vlen;R1A5S8bVi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1SbS8G0G0A2M1SfG0G0R2Sa1Vlen;A1A4S7G1A1M2A3G2S7S22A1S7S8G0ScA2A1A6Sa4Vflags;Vm;Vlen;R2A4S7S1eA1A4A3F_;Fa;").
  Proof using Hlen Hno Hshape.
    intros a Hp. apply check_spec_ok. rewrite mmap_rw_reduce.
    pose proof Hp as (_ & _ & Hc & _).
    assert (E : errno_ret_in (mmap_errnos_when (mmap_grant_refusable flags m (mmap_nZ len))) a = false)
      by (unfold mmap_errnos_when; exact (mmap_place_not_errno _ a (mmap_nZ len) (mmap_nZ_nonneg len) Hc)).
    rewrite E.
    pose proof (proj1 (mmap_place_okb _ _ _ _ _) Hp) as G.
    unfold addr, flags, len in G |- *.
    rewrite G. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma mmap_rw_intro_ok : ltac2:(tb__ "0|3|
S17Q40A1M0Sa7Vaddr;Vflags;Vm;Vlen;R1A5S106Vi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1SbS8G0G0A2M1SfG0G0R2Sa1Vlen;A1A4S7G1A1M2A3G2S7S22A1S7S8G0ScA2A1A6Sa4Vflags;Vm;Vlen;R2A4S7S1eA1A4A3F_;Fa;").
  Proof using Hlen Hno Hshape.
    intros. split; [eapply mmap_rw_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. match goal with Ha : mmap_place_ok _ _ _ _ ?a |- _ => pose proof (mmap_place_not_errno _ a (mmap_nZ len) (mmap_nZ_nonneg len) (proj1 (proj2 (proj2 Ha)))) as Hnot end. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.

  Lemma mmap_rw_not_refusable_place : ltac2:(tb__ "0|1|
S0SaSd2Vflags;Vm;S9fVlen;A1A3S10A3S2S17Q40A1M0G0Sa7Vaddr;Vflags;Vm;Vlen;R1A5La;A2F_;").
  Proof using .
    intros Hnr. unfold mmap_grant_refusable in Hnr.
    apply orb_false_iff in Hnr as [Hb Hg]. apply negb_false_iff in Hb. apply negb_false_iff in Hg.
    apply vm_gap_available_iff in Hg as (a & Hal & Hpos & Htop & Hfree).
    exists a. unfold mmap_place_ok. repeat split; try assumption.
  Qed.

  Lemma mmap_rw_inv_forced : ltac2:(tb__ "0|5|
S8dS1dA1M0S106Vi;Vm;R1A3S3S1S0SaSd2Vflags;Vm;S9fVlen;A1A3SdA3S9eR2S25S3bA1Vm;S7S1eA1M1A4A2S2S17Q40A1M2G2S1Sa7Vaddr;Vflags;Vm;Vlen;R1A5S0G0R3S8cS1dS23R1S7S8G2S9S17Q8A1A1A2A1SbS8G2G2A2M3SfG2G2R1Sa1Vlen;A1A4S7G3A1M4A3G4S7S22A1S7S8G2ScA2A1A6Sa4Vflags;Vm;Vlen;R1A4G1A4A3A2La;A2A2F_;FR;").
  Proof using Hlen Hno Hshape.
    intros R [Hs Hns]. destruct (mmap_rw_inv R Hs) as [He|Hg]; [left|right; exact Hg].
    split; [|exact He].
    destruct (mmap_grant_refusable flags m (mmap_nZ len)) eqn:F; [reflexivity|exfalso].
    destruct (mmap_rw_not_refusable_place F) as [a Ha].
    pose proof Ha as (_ & _ & Hc & _).
    pose proof (mmap_place_not_errno _ a (mmap_nZ len) (mmap_nZ_nonneg len) Hc) as Hne.
    unfold is_ret in He. subst R.
    pose proof (ns_enomem_mmap i m _ _ _ _ (Hns _ _ _ eq_refl eq_refl) Hno eq_refl (mmap_rw_intro_ok a Ha)) as X.
    cbn [eff_ret] in X. rewrite X in Hne. vm_compute in Hne. discriminate Hne.
  Qed.

  Lemma mmap_rw_inv_granted : ltac2:(tb__ "0|4|
S8dS1dA1M0S0SaSd2Vflags;Vm;S9fVlen;A1A3S10A3S106Vi;Vm;R2A3S2S17Q40A1M1G1S1Sa7Vaddr;Vflags;Vm;Vlen;R1A5S0G0R4S8cS1dS23R1S7S8G1S9S17Q8A1A1A2A1SbS8G1G1A2M2SfG1G1R1Sa1Vlen;A1A4S7G2A1M3A3G3S7S22A1S7S8G1ScA2A1A6Sa4Vflags;Vm;Vlen;R1A4S7S1eA1A4A3A2La;A2F_;F_;FR;").
  Proof using Hlen Hno Hshape.
    intros R Hnr Hs. destruct (mmap_rw_inv_forced R Hs) as [[Hr _]|H]; [|exact H].
    rewrite Hnr in Hr. discriminate.
  Qed.

  Lemma mmap_rw_intro_some : ltac2:(tb__ "0|1|
S2S8dS1dA1M0G0S8bVi;Vm;R1A3LR;A2").
  Proof using Hlen Hno Hshape.
    destruct (mmap_grant_refusable flags m (mmap_nZ len)) eqn:Hrf.
    - eexists. exact (mmap_rw_intro_fail Hrf).
    - destruct (mmap_rw_not_refusable_place Hrf) as [a Ha]. eexists. exact (mmap_rw_intro_ok a Ha).
  Qed.
End MmapRW.

Section MmapNone.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0SaSd3S21Vi;U2A2S21Vi;U3A2S21Vi;U5A2A3SdA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0SaScfS21Vi;U2A2S21Vi;U3A2S21Vi;U5A2A3S10A3").

  Lemma mmap_none_reduce : ltac2:(tb__ "0|11|
S1dS0S80Sb7Vi;R1Vm;A3S1dS80Leff;R1S17Q40M0A1M1S9S8G1S9S17Q8A1A1A2M2A1M3S9S8G1G1A2M4A1M5G5S9S22A1M6S9S8G1ScA2M7A1M8G3S80Leff_writes;R5G5S80Leff_zeros;R4G6S80Leff_copies;R2G8S80Leff_copyins;R1SaS80L_;M9S85SdfSd5Vm;S9fVlen;A1MaA2A1R6A2G5S80Lus;R3S82Vm;S7S1eA1MbA2G4G5S81Ll;Lp;McX9x2G9S13S13S13S13S95S93S18G0R6A2MdS32A2Z0MeA2S98GeGdA2A2S94S91GdGaA2S35S20Vm;A1MfA1A2A2S3fS15G4S36GfA1S2eGfA1A3R6Sa1Vlen;A1M10A3A2S86R3SbG4SfG1G1R6G10A4S7G4A1A3A2A2S82Sa3Vflags;Vm;Vlen;R6A4GbA2S81Xax2Xax2G7G8S81Ll;Lp;X9x2S22G6S81Ll;Lm0;X9x2GcX9x2G2G3S81Ll;Lp;X9x2Leff_copyins;Leff_copies;Lus;Leff_zeros;Leff_writes;Lr;X1dx1A3Feff;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_noaccess_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hshape. reflexivity.
  Qed.

  Lemma mmap_none_inv : ltac2:(tb__ "0|5|
S8dS1dA1M0S8bVi;Vm;R1A3S3S9eR2S25S3bA1Vm;S7S1eA1M1A4S2S17Q40A1M2G2S1Sa8Vaddr;Vm;Vlen;R1A4S0G0R3S8cS1dS23R1S7S8G2S9S17Q8A1A1A2A1S7S8G2G2A2M3A1M4SbG3SfG2G2R1Sa1Vlen;A1A4G4A3S7S22A1S7S8G2ScA2A1A6Sa3Vflags;Vm;Vlen;R1A4G1A4A3A2La;A2A2F_;FR;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_none_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in (mmap_errnos_when (mmap_reserve_refusable m (mmap_nZ len))) r) eqn:E.
      + destruct us; [|discriminate].
        unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->).
        destruct Hin as [<-|[]]. inversion Hs; subst. left. reflexivity.
      + right. exists r.
        match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G; [|discriminate] end.
        apply andb_true_iff in G as [G Gz]. apply listNN_eqb_eq in Gz. subst us.
        inversion Hs; subst. split; [|reflexivity].
        apply mmap_place_ok_noneb. exact G.
    - exfalso. specialize (Hs probe_eff). rewrite mmap_none_reduce in Hs. unfold probe_eff in Hs.
      destruct (errno_ret_in _ (Z_to_bv 64 0)); [discriminate|].
      match type of Hs with (if ?c then _ else _) = _ => destruct c; discriminate end.
  Qed.

  Lemma mmap_none_intro_fail_ss : ltac2:(tb__ "0|2|
S0SaSd5Vm;S9fVlen;A1A2SdA3S8bVi;Vm;S8cS1dS23S25S3bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros Hrf. apply check_spec_ok. rewrite mmap_none_reduce. rewrite Hrf. unfold mmap_errnos_when.
    rewrite (errno_ret_in_intro mmap_errnos ENOMEM ltac:(left; reflexivity)). reflexivity.
  Qed.

  Lemma mmap_none_intro_fail : ltac2:(tb__ "0|2|
S0SaSd5Vm;S9fVlen;A1A2SdA3S106Vi;Vm;S8cS1dS23S25S3bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros. split; [eapply mmap_none_intro_fail_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_forced_mmap; [assumption|]. intros ? ? ? Hs'. destruct (mmap_none_inv _ Hs') as [He | (a & (Hal & Hpos & Htop & Hfree) & E')]; [unfold is_ret in He; inversion He; subst; reflexivity | exfalso; unfold mmap_n in Hfree; match goal with F : mmap_reserve_refusable _ _ = true |- _ => rewrite (reserve_not_refusable_of _ _ _ Hal Hpos Htop Hfree) in F; discriminate F end].
  Qed.

  Lemma mmap_none_intro_ok_ss : ltac2:(tb__ "0|3|
S17Q40A1M0Sa8Vaddr;Vm;Vlen;R1A4S8bVi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2M1A1M2SbG1SfG0G0R2Sa1Vlen;A1A4G2A3S7S22A1S7S8G0ScA2A1A6Sa3Vflags;Vm;Vlen;R2A4S7S1eA1A4A3F_;Fa;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros a Hp. apply check_spec_ok. rewrite mmap_none_reduce.
    pose proof Hp as (_ & _ & Hc & _).
    assert (E : errno_ret_in (mmap_errnos_when (mmap_reserve_refusable m (mmap_nZ len))) a = false)
      by (unfold mmap_errnos_when; exact (mmap_place_not_errno _ a (mmap_nZ len) (mmap_nZ_nonneg len) Hc)).
    rewrite E.
    pose proof (proj1 (mmap_place_ok_noneb _ _ _ _) Hp) as G. unfold addr, flags, len in G |- *.
    rewrite G. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma mmap_none_intro_ok : ltac2:(tb__ "0|3|
S17Q40A1M0Sa8Vaddr;Vm;Vlen;R1A4S106Vi;Vm;S8cS1dS23R2S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2M1A1M2SbG1SfG0G0R2Sa1Vlen;A1A4G2A3S7S22A1S7S8G0ScA2A1A6Sa3Vflags;Vm;Vlen;R2A4S7S1eA1A4A3F_;Fa;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros. split; [eapply mmap_none_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. match goal with Ha : mmap_place_ok_none _ _ _ ?a |- _ => pose proof (mmap_place_not_errno _ a (mmap_nZ len) (mmap_nZ_nonneg len) (proj1 (proj2 (proj2 Ha)))) as Hnot end. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.

  Lemma mmap_none_not_refusable_place : ltac2:(tb__ "0|1|
S0SaSd5Vm;S9fVlen;A1A2S10A3S2S17Q40A1M0G0Sa8Vaddr;Vm;Vlen;R1A4La;A2F_;").
  Proof using .
    intros Hnr. unfold mmap_reserve_refusable in Hnr. apply negb_false_iff in Hnr.
    apply vm_gap_available_iff in Hnr as (a & Hal & Hpos & Htop & Hfree).
    exists a. unfold mmap_place_ok_none. repeat split; try assumption.
  Qed.

  Lemma mmap_none_inv_forced : ltac2:(tb__ "0|5|
S8dS1dA1M0S106Vi;Vm;R1A3S3S1S0SaSd5Vm;S9fVlen;A1A2SdA3S9eR2S25S3bA1Vm;S7S1eA1M1A4A2S2S17Q40A1M2G2S1Sa8Vaddr;Vm;Vlen;R1A4S0G0R3S8cS1dS23R1S7S8G2S9S17Q8A1A1A2A1S7S8G2G2A2M3A1M4SbG3SfG2G2R1Sa1Vlen;A1A4G4A3S7S22A1S7S8G2ScA2A1A6Sa3Vflags;Vm;Vlen;R1A4G1A4A3A2La;A2A2F_;FR;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros R [Hs Hns]. destruct (mmap_none_inv R Hs) as [He|Hg]; [left|right; exact Hg].
    split; [|exact He].
    destruct (mmap_reserve_refusable m (mmap_nZ len)) eqn:F; [reflexivity|exfalso].
    destruct (mmap_none_not_refusable_place F) as [a Ha].
    pose proof Ha as (_ & _ & Hc & _).
    pose proof (mmap_place_not_errno _ a (mmap_nZ len) (mmap_nZ_nonneg len) Hc) as Hne.
    unfold is_ret in He. subst R.
    pose proof (ns_enomem_mmap i m _ _ _ _ (Hns _ _ _ eq_refl eq_refl) Hno eq_refl (mmap_none_intro_ok a Ha)) as X.
    cbn [eff_ret] in X. rewrite X in Hne. vm_compute in Hne. discriminate Hne.
  Qed.

  Lemma mmap_none_inv_granted : ltac2:(tb__ "0|4|
S8dS1dA1M0S0SaSd5Vm;S9fVlen;A1A2S10A3S106Vi;Vm;R2A3S2S17Q40A1M1G1S1Sa8Vaddr;Vm;Vlen;R1A4S0G0R4S8cS1dS23R1S7S8G1S9S17Q8A1A1A2A1S7S8G1G1A2M2A1M3SbG2SfG1G1R1Sa1Vlen;A1A4G3A3S7S22A1S7S8G1ScA2A1A6Sa3Vflags;Vm;Vlen;R1A4S7S1eA1A4A3A2La;A2F_;F_;FR;").
  Proof using Hlen Hno Hnot_rw Hshape.
    intros R Hnr Hs. destruct (mmap_none_inv_forced R Hs) as [[Hr _]|H]; [|exact H].
    rewrite Hnr in Hr. discriminate.
  Qed.

  Lemma mmap_none_intro_some : ltac2:(tb__ "0|1|
S2S8dS1dA1M0G0S8bVi;Vm;R1A3LR;A2").
  Proof using Hlen Hno Hnot_rw Hshape.
    destruct (mmap_reserve_refusable m (mmap_nZ len)) eqn:Hrf.
    - eexists. exact (mmap_none_intro_fail Hrf).
    - destruct (mmap_none_not_refusable_place Hrf) as [a Ha]. eexists. exact (mmap_none_intro_ok a Ha).
  Qed.
End MmapNone.

Definition mmap_fixed_ok_vm (h : VmMaps) (addr n : word) : VmMaps := ltac2:(tb__ "0|3|
S43S36Vh;A1S2eVh;A1SbS8S17Q40M0A1M1G1A2SfG1G1Vaddr;Vn;A4S50S39Vh;A1S18G0Vaddr;A2M2S91G2S18G0Vn;A2A2A3A3S3aVh;A1S2bVh;A1S44Vh;A1S4aVh;A1S26Vh;A1A8").
Definition mmap_fixed_dead_vm (h : VmMaps) (addr n : word) : VmMaps := ltac2:(tb__ "0|3|
S43S36Vh;A1S50S2eVh;A1S18Q40M0Vaddr;A2M1S91G1S18G0Vn;A2A2M2A3S50S39Vh;A1G1G2A3S3aVh;A1S2bVh;A1S44Vh;A1S4aVh;A1S26Vh;A1A8").

Definition mmap_fixed_ok_model (flags : word) (m : Model) (addr n : word) : Model := ltac2:(tb__ "0|0|
SeaVflags;Vaddr;Vn;S3cSb3S20Vm;A1Vaddr;Vn;A3Vm;A2A4").
Definition mmap_fixed_dead_model (m : Model) (addr n : word) : Model := ltac2:(tb__ "0|0|
Se2Vaddr;Vn;Sb0S20Vm;A1Vaddr;Vn;A3Vm;A4").

Lemma mmap_fixed_dead_vm_spec : ltac2:(tb__ "0|1|
S29S17Q40A1M0G0S0S29Sb0R3R2R1A3Se9R3R2R1A3A3Fn;Faddr;Fh;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_mmap_fixed_ok_model : ltac2:(tb__ "0|1|
S17Q40A1M0S1fG0G0S0G0S26S20Sa6R4R3R2R1A4A1A1S26S20R3A1A1A3Fn;Faddr;Fm;Fflags;").
Proof.
  intros. unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. reflexivity.
Qed.
Lemma vm_init_sp_mmap_fixed_dead_model : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S0G0S26S20SacR3R2R1A3A1A1S26S20R3A1A1A3Fn;Faddr;Fm;").
Proof. reflexivity. Qed.

Section MmapFixed.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0SaSe0S21Vi;U2A2S21Vi;U3A2S21Vi;U5A2A3SdA3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0SaSd3S21Vi;U2A2S21Vi;U3A2S21Vi;U5A2A3S10A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0SaScfS21Vi;U2A2S21Vi;U3A2S21Vi;U5A2A3S10A3").

  Hypothesis Hceil : ltac2:(tb__ "0|0|
S8fS91S18Q40Vaddr;A2S9fVlen;A1A2S35S20Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S7fS93S18Q40Vaddr;A2S32A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.

  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0SaS3fS36Vh;A1Vaddr;Vn;A3SdA3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0SaS48S2eVh;A1Vaddr;Vn;A3SdA3").

  Lemma mmap_fixed_reduce : forall eff, check_syscall i eff m =
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with
             | [] => CheckOk m []
             | _ => if listNN_eqb us [(addr, n)]
                    then CheckOk (mmap_fixed_dead_model m addr n) []
                    else CheckReject
             end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (mmap_fixed_ok_model flags m addr n) []
        else CheckReject
    | _ => CheckReject
    end.
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_fixed_noaccess_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hnot_none, Hshape.
    unfold n, h, len, addr, flags, mmap_n, mmap_nZ in *. cbv zeta. cbn [negb].
    pose proof (alloc_top_lt (m_vmmaps m)) as Hc.
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E1.
    { apply Z.leb_le in E1. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
    rewrite Halign. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
    rewrite Hfree, Hcont. cbn [andb].
    reflexivity.
  Qed.

  Lemma errno_ret_in_nil : ltac2:(tb__ "0|0|
S17Q40A1S0SaS85S7S7fA1R1A2S10A3Fr;").
  Proof. reflexivity. Qed.

  Lemma mmap_fixed_inv : ltac2:(tb__ "0|a|
S8dS1dA1M0S8bVi;Vm;R1A3S3S9eR2S25S3bA1M1Vm;S7S1eA1M2A4S3S0G0R2S8cS1dS23Vaddr;S7S8S17Q40A1M3S9S17Q8A1A1A2A1M4S7S8G3G3A2M5A1M6SbG5SfG3G3Vaddr;Vn;A4G6A3M7S7S22A1M8S7S8G3ScA2A1M9A6Sa6Vflags;Vm;Vaddr;Vn;A4G2A4A3S0G0R2S8cS1dS23G1G4G6G7G8G9A6SacVm;Vaddr;Vn;A3G2A4A3A2A2F_;FR;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_fixed_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:E.
      + apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
        destruct us as [|u us]; [inversion Hs; subst; left; reflexivity|].
        destruct (listNN_eqb (u :: us) [(addr, n)]) eqn:G; [|discriminate].
        apply listNN_eqb_eq in G. injection G as -> ->.
        inversion Hs; subst. right; right; reflexivity.
      + destruct (bv_eqb r addr && listNN_eqb us [(addr, n)]) eqn:G; [|discriminate].
        apply andb_true_iff in G as [G1 G2]. apply bv_eqb_eq in G1. apply listNN_eqb_eq in G2.
        subst. inversion Hs; subst. right; left; reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite mmap_fixed_reduce in Hs. unfold probe_eff in Hs.
      check_shape_discriminate Hs.
  Qed.

  Lemma mmap_fixed_addr_not_errno : errno_ret_in mmap_errnos addr = false.
  Proof using Hceil.
    exact (mmap_place_not_errno (m_vmmaps m) addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil).
  Qed.


  Lemma mmap_fixed_intro_ok_ss : ltac2:(tb__ "0|3|
S8bVi;Vm;S8cS1dS23Vaddr;S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2M1A1M2SbG1SfG0G0Vaddr;Vn;A4G2A3S7S22A1S7S8G0ScA2A1A6Sa6Vflags;Vm;Vaddr;Vn;A4S7S1eA1A4A3").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    apply check_spec_ok. rewrite mmap_fixed_reduce. cbv beta iota.
    rewrite mmap_fixed_addr_not_errno.
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma mmap_fixed_intro_ok : ltac2:(tb__ "0|3|
S106Vi;Vm;S8cS1dS23Vaddr;S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2M1A1M2SbG1SfG0G0Vaddr;Vn;A4G2A3S7S22A1S7S8G0ScA2A1A6Sa6Vflags;Vm;Vaddr;Vn;A4S7S1eA1A4A3").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_fixed_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. pose proof mmap_fixed_addr_not_errno as Hnot. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.

  Lemma mmap_fixed_inv_ok : ltac2:(tb__ "0|4|
S8dS1dA1M0S106Vi;Vm;R1A3S0G0R2S8cS1dS23Vaddr;S7S8S17Q40A1M1S9S17Q8A1A1A2A1S7S8G1G1A2M2A1M3SbG2SfG1G1Vaddr;Vn;A4G3A3S7S22A1S7S8G1ScA2A1A6Sa6Vflags;Vm;Vaddr;Vn;A4S7S1eA1A4A3F_;FR;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros R [Hs Hns]. destruct (mmap_fixed_inv R Hs) as [He | [Hok | Hdead]]; [exfalso | exact Hok | exfalso].
    - unfold is_ret in He. subst R.
      pose proof (ns_enomem_mmap i m _ _ _ _ (Hns _ _ _ eq_refl eq_refl) Hno eq_refl mmap_fixed_intro_ok) as X.
      cbn [eff_ret] in X. pose proof mmap_fixed_addr_not_errno as Hne.
      rewrite X in Hne. vm_compute in Hne. discriminate Hne.
    - subst R.
      assert (Hg : m_halted (mmap_fixed_dead_model m addr n) = m_halted m)
        by (unfold mmap_fixed_dead_model, with_mmap_destroyed; autorewrite with model; reflexivity).
      pose proof (ns_enomem_mmap i m _ _ _ _ (Hns _ _ _ eq_refl Hg) Hno eq_refl mmap_fixed_intro_ok) as X.
      cbn [eff_ret] in X. pose proof mmap_fixed_addr_not_errno as Hne.
      rewrite X in Hne. vm_compute in Hne. discriminate Hne.
  Qed.

  Lemma mmap_fixed_intro_some : ltac2:(tb__ "0|1|
S2S8dS1dA1M0G0S8bVi;Vm;R1A3LR;A2").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    eexists. exact mmap_fixed_intro_ok.
  Qed.
End MmapFixed.

Definition munmap_vm (h : VmMaps) (addr n : word) : VmMaps := ltac2:(tb__ "0|2|
S43S36Vh;A1S78S2eVh;A1Vaddr;A2S50S39Vh;A1S18Q40M0Vaddr;A2M1S91G1S18G0Vn;A2A2A3S3aVh;A1S2bVh;A1S44Vh;A1S4aVh;A1S26Vh;A1A8").

Definition munmap_model (m : Model) (addr n : word) : Model := ltac2:(tb__ "0|0|
Se2Vaddr;Vn;Sb6S20Vm;A1Vaddr;Vn;A3Vm;A4").

Lemma vm_init_sp_munmap_model : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S0G0S26S20SabR3R2R1A3A1A1S26S20R3A1A1A3Fn;Faddr;Fm;").
Proof. reflexivity. Qed.

Section Munmap.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 215%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let h := m_vmmaps m.
  Let n := mmap_n len.

  Lemma munmap_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3S101Vaddr;Vlen;R1Vm;A4A3Feff;").
  Proof using Hno. intros eff. dispatch Hno. reflexivity. Qed.

  Lemma munmap_einval_check : ltac2:(tb__ "0|2|
S1dS3S5S0S7fS93S18Q40M0Vaddr;A2S32A2Z0M1A3A1S0S17G0A1Vlen;S19G0G1A2A3A2S0S80Sb7Vi;R2Vm;A3S83R2S25S59A1Vm;S7S1eA1A4A3F_;Feff;").
  Proof using Hno.
    intros eff Hbad. rewrite munmap_check. unfold check_munmap. unfold n, h, len, addr in *.
    destruct Hbad as [Ha | E].
    - apply Z.eqb_neq in Ha. rewrite Ha. reflexivity.
    - rewrite E. change (w_is0 (Z_to_bv 64 0)) with true. rewrite orb_true_r. reflexivity.
  Qed.

  Lemma munmap_einval_inv : ltac2:(tb__ "0|2|
S8dS1dA1S3S5S0S7fS93S18Q40M0Vaddr;A2S32A2Z0M1A3A1S0S17G0A1Vlen;S19G0G1A2A3A2S8bVi;Vm;R2A3S9eR3S25S59A1Vm;S7S1eA1A4F_;F_;FR;").
  Proof using Hno. intros R Hbad. apply check_of_ret_only. intros; apply munmap_einval_check, Hbad. Qed.

  Lemma munmap_einval_intro_ss : ltac2:(tb__ "0|4|
S3S5S0S7fS93S18Q40M0Vaddr;A2S32A2Z0M1A3A1S0S17G0A1M2Vlen;S19G0G1A2A3A2S8bVi;Vm;S8cS1dS23S25S59A1S7S8G2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1S7S8G2ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hno. intros Hbad. apply intro_ret_only. intros; apply munmap_einval_check, Hbad. Qed.

  Lemma munmap_einval_intro : ltac2:(tb__ "0|4|
S3S5S0S7fS93S18Q40M0Vaddr;A2S32A2Z0M1A3A1S0S17G0A1M2Vlen;S19G0G1A2A3A2S106Vi;Vm;S8cS1dS23S25S59A1S7S8G2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1S7S8G2ScA2A1A6Vm;S7S1eA1A4A3F_;").
  Proof using Hno.
    intros. split; [eapply munmap_einval_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S7fS93S18Q40Vaddr;A2S32A2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.

  Hypothesis Htask : ltac2:(tb__ "0|0|
S8fS91S18Q40Vaddr;A2S9fVlen;A1A2S41A2").

  Lemma munmap_gates : ltac2:(tb__ "0|b|
S1dS0S80Sb7Vi;R1Vm;A3SaS80L_;M0S4cS2eVh;A1Vaddr;Vn;A3S1dS80Leff;R1S17Q40M1A1M2S9S8G2S9S17Q8A1A1A2M3A1M4S9S8G2G2A2M5A1M6G6S9S22A1M7S9S8G2ScA2M8A1M9G4S80Leff_writes;R5G6S80Leff_zeros;R4G7S80Leff_copies;R2G9S80Leff_copyins;R1G0S13SbcR6A1S86R3SbG5SfG2G2Vaddr;Vn;A4S7G5A1A3A2A2S82SabVm;Vaddr;Vn;A3S7S1eA1MaA2S81Xax2G8G9S81Ll;Lp;X9x2S22G7S81Ll;Lm0;X9x2G5G6S81Ll;Lp;X9x2G3G4S81Ll;Lp;X9x2Leff_copyins;Leff_copies;Lus;Leff_zeros;Leff_writes;Lr;X1dx1G0SdbVh;Vaddr;S9fVlen;A1A3S83R1S19G1Z0A2Vm;GaA4S84Xax2Xax2A3Feff;").
  Proof using Halign Hlen Hno Htask.
    intros eff. rewrite munmap_check. unfold check_munmap. unfold n, h, len, addr, mmap_n, mmap_nZ in *.
    rewrite Halign. rewrite (mmap_len_gate i Hlen). cbn [Z.eqb negb orb].
    cbv zeta. destruct (TASK_SIZE <? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E.
    { apply Z.ltb_lt in E. lia. }
    reflexivity.
  Qed.

  Lemma munmap_exact_inv : ltac2:(tb__ "0|5|
S8dS1dA1M0S0SaS4cS2eVh;A1Vaddr;Vn;A3SdA3S8bVi;Vm;R2A3S0G0R3S8cS1dS23S19Q40M1Z0A2S7S8S17G1A1M2S9S17Q8A1A1A2A1S7S8G2G2A2M3A1M4SbG3SfG2G2Vaddr;Vn;A4G4A3S7S22A1S7S8G2ScA2A1A6SabVm;Vaddr;Vn;A3S7S1eA1A4A3F_;F_;FR;").
  Proof using Halign Hlen Hno Htask.
    intros R Hhas Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite munmap_gates, Hhas in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (w_is0 r && listNN_eqb us [(addr, n)]) eqn:G; [|discriminate].
      apply andb_true_iff in G as [G1 G2]. apply w_is0_spec in G1. apply listNN_eqb_eq in G2.
      subst. inversion Hs; subst. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite munmap_gates, Hhas in Hs. unfold probe_eff in Hs.
      cbn in Hs. discriminate.
  Qed.

  Lemma munmap_exact_intro_ss : ltac2:(tb__ "0|4|
S0SaS4cS2eVh;A1Vaddr;Vn;A3SdA3S8bVi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2M2A1M3SbG2SfG1G1Vaddr;Vn;A4G3A3S7S22A1S7S8G1ScA2A1A6SabVm;Vaddr;Vn;A3S7S1eA1A4A3F_;").
  Proof using Halign Hlen Hno Htask.
    intros Hhas. apply check_spec_ok. rewrite munmap_gates, Hhas.
    change (w_is0 (Z_to_bv 64 0)) with true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma munmap_exact_intro : ltac2:(tb__ "0|4|
S0SaS4cS2eVh;A1Vaddr;Vn;A3SdA3S106Vi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2M2A1M3SbG2SfG1G1Vaddr;Vn;A4G3A3S7S22A1S7S8G1ScA2A1A6SabVm;Vaddr;Vn;A3S7S1eA1A4A3F_;").
  Proof using Halign Hlen Hno Htask.
    intros. split; [eapply munmap_exact_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma munmap_free_inv : ltac2:(tb__ "0|0|
S8dS1dA1S0SaS4cS2eVh;A1Vaddr;Vn;A3S10A3S0SaSdbVh;Vaddr;S9fVlen;A1A3SdA3S8bVi;Vm;R3A3S9eR4S19Q40Z0A2Vm;S7S1eA1A4F_;F_;F_;FR;").
  Proof using Halign Hlen Hno Htask.
    intros R Hhas Hrf. apply check_of_ret_only. intros eff. rewrite munmap_gates, Hhas, Hrf. reflexivity.
  Qed.

  Lemma munmap_free_intro_ss : ltac2:(tb__ "0|3|
S0SaS4cS2eVh;A1Vaddr;Vn;A3S10A3S0SaSdbVh;Vaddr;S9fVlen;A1A3SdA3S8bVi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6Vm;S7S1eA1A4A3F_;F_;").
  Proof using Halign Hlen Hno Htask.
    intros Hhas Hrf. apply intro_ret_only. intros eff. rewrite munmap_gates, Hhas, Hrf. reflexivity.
  Qed.

  Lemma munmap_free_intro : ltac2:(tb__ "0|3|
S0SaS4cS2eVh;A1Vaddr;Vn;A3S10A3S0SaSdbVh;Vaddr;S9fVlen;A1A3SdA3S106Vi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6Vm;S7S1eA1A4A3F_;F_;").
  Proof using Halign Hlen Hno Htask.
    intros. split; [eapply munmap_free_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.

  Lemma munmap_other_unmodeled : ltac2:(tb__ "0|0|
S0SaS4cS2eVh;A1Vaddr;Vn;A3S10A3S0SaSdbVh;Vaddr;S9fVlen;A1A3S10A3S8bVi;Vm;S8eS1dA1A3F_;F_;").
  Proof using Halign Hlen Hno Htask.
    intros Hhas Hrf. apply (check_syscall_sound_unmodeled _ probe_eff).
    rewrite munmap_gates, Hhas, Hrf. reflexivity.
  Qed.
End Munmap.

Lemma mprotect_rw_b : ltac2:(tb__ "0|1|
S17Q40M0A1S0S7fS18G0R1A2Z3A3S1S0SaSefR2A1SdA3S0SaSeeR2A1S10A3A2F_;Fprot;").
Proof.
  intros prot Hp. unfold mprotect_modeled_b, mprotect_grows_conflict_b. rewrite Hp.
  split; reflexivity.
Qed.

Section Mprotect.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 226%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hprot : bv_unsigned (in_arg i 2) = 3%Z.
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S7fS93S18Q40Vaddr;A2S32A2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S92S91S18Q40Vaddr;A2S9fVlen;A1A2S53A2").

  Lemma mprotect_gates : ltac2:(tb__ "0|17|
S1dS0S80Sb7Vi;R1Vm;A3SaS80L_;M0S13S48S39Vh;A1M1Vaddr;Vn;A3S48S2eVh;A1Vaddr;Vn;A3M2A2S1dS80Leff;M3R1S17Q40A1M4S9S8G4S9S17Q8A1A1A2M5A1M6S9S8G4G4A2M7A1M8G8S9S22A1M9S9S8G4ScA2MaA1MbG6S80Leff_writes;McR5G8S80Leff_unmaps;MdR3G9S80Leff_copies;MeR2GbS80Leff_copyins;MfR1G0S85SedSf0Vm;Vaddr;Vn;A3A1R6A2G8S80Lzs;R4S82Vm;S7S1eA1M10A2M11G7G8S81Ll;Lp;M12X9x2G0S13S13SecVm;Vaddr;Vn;A3SbcR6A1M13A2S86R4SbG7SfG4G4Vaddr;Vn;A4S7G7A1A3A2A2S82SebVm;Vaddr;Vn;A3G10A2S81Xax2Xax2GaGbS81Ll;Lp;M14X9x2S22G9S81Ll;Lm0;M15X9x2G12X9x2G5G6S81Ll;Lp;M16X9x2Leff_copyins;Leff_copies;Leff_unmaps;Lzs;Leff_writes;Lr;X1dx1G0S13G2S3fG1Vaddr;Vn;A3A2G3R1G4G6G8G8G9GbGcR5G8S80Leff_zeros;R4GdR3GeR2GfR1G0G13G11S81Xax2G14X9x2G15X9x2G12X9x2G12X9x2G16X9x2Leff_copyins;Leff_copies;Leff_unmaps;Leff_zeros;Leff_writes;Lr;X1dx1S84Xax2Xax2A3Feff;").
  Proof using Halign Hlen Hno Hprot Hwrap.
    intros eff. dispatch Hno. unfold check_mprotect. unfold n, h, len, addr, mmap_n, mmap_nZ in *.
    destruct (mprotect_rw_b _ Hprot) as [Hm Hg]. rewrite Hg, Hm.
    rewrite Halign. rewrite (mmap_len_gate i Hlen). cbn [Z.eqb negb].
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E.
    { apply Z.leb_le in E. lia. }
    cbv zeta. reflexivity.
  Qed.

  Section Expose.
    Hypothesis Hna : ltac2:(tb__ "0|0|
S0SaS48S39Vh;A1Vaddr;Vn;A3SdA3").
    Hypothesis Hmp : ltac2:(tb__ "0|0|
S0SaS48S2eVh;A1Vaddr;Vn;A3SdA3").

    Lemma mprotect_expose_inv : ltac2:(tb__ "0|6|
S8dS1dA1M0S8bVi;Vm;R1A3S3S9eR2S25S3bA1Vm;S7S1eA1M1A4S1S0SaSecVm;Vaddr;Vn;A3SdA3S0G0R2S8cS1dS23S19Q40M2Z0A2S7S8S17G2A1M3S9S17Q8A1A1A2A1SbS8G3G3A2M4SfG3G3Vaddr;Vn;A4S7G4A1M5A3G5S7S22A1S7S8G3ScA2A1A6SebVm;Vaddr;Vn;A3G1A4A3A2A2F_;FR;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
      - rewrite mprotect_gates, Hna, Hmp in Hs. cbn [andb] in Hs.
        destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate].
        destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate].
        destruct ci; [|destruct zs; discriminate].
        destruct (errno_ret_in (mprotect_errnos_when (mprotect_refusable m addr n)) r) eqn:E.
        + destruct zs; [|discriminate].
          unfold mprotect_errnos_when in E.
          apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
          inversion Hs; subst. left. reflexivity.
        + destruct (mprotect_budget_ok m addr n && w_is0 r && listNN_eqb zs [(addr, n)]) eqn:G; [|discriminate].
          apply andb_true_iff in G as [G G2]. apply andb_true_iff in G as [G0 G1].
          apply w_is0_spec in G1. apply listNN_eqb_eq in G2.
          subst. inversion Hs; subst. right. split; [exact G0|reflexivity].
      - exfalso. specialize (Hs probe_eff). rewrite mprotect_gates, Hna, Hmp in Hs.
        unfold probe_eff in Hs. cbn -[mprotect_budget_ok mprotect_errnos_when mprotect_refusable errno_ret_in] in Hs.
        destruct (errno_ret_in (mprotect_errnos_when (mprotect_refusable m addr n)) (Z_to_bv 64 0)) eqn:E.
        + unfold mprotect_errnos_when in E.
          apply errno_ret_in_true in E as (e & Hin & He). destruct Hin as [<-|[]]. discriminate He.
        + destruct (mprotect_budget_ok m addr n); discriminate.
    Qed.


    Lemma mprotect_expose_intro_fail_ss : ltac2:(tb__ "0|2|
S0SaSecVm;Vaddr;Vn;A3S10A3S8bVi;Vm;S8cS1dS23S25S3bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros Hb. apply check_spec_ok. rewrite mprotect_gates, Hna, Hmp. cbn [andb].
      unfold mprotect_errnos_when.
      rewrite (errno_ret_in_intro mprotect_errnos ENOMEM ltac:(left; reflexivity)). reflexivity.
    Qed.

    Lemma mprotect_expose_intro_fail : ltac2:(tb__ "0|2|
S0SaSecVm;Vaddr;Vn;A3S10A3S106Vi;Vm;S8cS1dS23S25S3bA1S7S8S17Q40A1M0S9S17Q8A1A1A2A1S7S8G0G0A2A1M1G1S7S22A1S7S8G0ScA2A1A6Vm;S7S1eA1A4A3F_;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros. split; [eapply mprotect_expose_intro_fail_ss; eassumption|].
      intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_forced_mprotect; [assumption|]. intros ? ? ? Hs'. destruct (mprotect_expose_inv _ Hs') as [He | (Hb & E')]; [unfold is_ret in He; inversion He; subst; reflexivity | congruence].
    Qed.

    Lemma mprotect_expose_intro_ok_ss : ltac2:(tb__ "0|4|
S0SaSecVm;Vaddr;Vn;A3SdA3S8bVi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1SbS8G1G1A2M2SfG1G1Vaddr;Vn;A4S7G2A1M3A3G3S7S22A1S7S8G1ScA2A1A6SebVm;Vaddr;Vn;A3S7S1eA1A4A3F_;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros Hb. apply check_spec_ok. rewrite mprotect_gates, Hna, Hmp. cbn [andb].
      unfold mprotect_errnos_when. rewrite Hb. cbn [andb].
      change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false.
      change (w_is0 (Z_to_bv 64 0)) with true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    Qed.

    Lemma mprotect_expose_intro_ok : ltac2:(tb__ "0|4|
S0SaSecVm;Vaddr;Vn;A3SdA3S106Vi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1SbS8G1G1A2M2SfG1G1Vaddr;Vn;A4S7G2A1M3A3G3S7S22A1S7S8G1ScA2A1A6SebVm;Vaddr;Vn;A3S7S1eA1A4A3F_;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros. split; [eapply mprotect_expose_intro_ok_ss; eassumption|].
      intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_nonenomem_mprotect; [assumption|]. cbn [eff_ret]. exact ret_zero_not_enomem.
    Qed.

    Lemma mprotect_expose_inv_forced : ltac2:(tb__ "0|7|
S8dS1dA1M0S106Vi;Vm;R1A3S3S1S0SaSecVm;Vaddr;Vn;A3M1S10A3S9eR2S25S3bA1Vm;S7S1eA1M2A4A2S1S0SaG1SdA3S0G0R2S8cS1dS23S19Q40M3Z0A2S7S8S17G3A1M4S9S17Q8A1A1A2A1SbS8G4G4A2M5SfG4G4Vaddr;Vn;A4S7G5A1M6A3G6S7S22A1S7S8G4ScA2A1A6SebVm;Vaddr;Vn;A3G2A4A3A2A2F_;FR;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros R [Hs Hns]. destruct (mprotect_expose_inv R Hs) as [He|Hg]; [left|right; exact Hg].
      split; [|exact He].
      destruct (mprotect_budget_ok m addr n) eqn:F; [exfalso|reflexivity].
      unfold is_ret in He. subst R.
      pose proof (ns_enomem_mprotect i m _ _ _ _ (Hns _ _ _ eq_refl eq_refl) Hno eq_refl (mprotect_expose_intro_ok F)) as X.
      cbn [eff_ret] in X. vm_compute in X. discriminate X.
    Qed.

    Lemma mprotect_expose_inv_granted : ltac2:(tb__ "0|5|
S8dS1dA1M0S0SaSecVm;Vaddr;Vn;A3SdA3S106Vi;Vm;R2A3S0G0R3S8cS1dS23S19Q40M1Z0A2S7S8S17G1A1M2S9S17Q8A1A1A2A1SbS8G2G2A2M3SfG2G2Vaddr;Vn;A4S7G3A1M4A3G4S7S22A1S7S8G2ScA2A1A6SebVm;Vaddr;Vn;A3S7S1eA1A4A3F_;F_;FR;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      intros R Hb Hs. destruct (mprotect_expose_inv_forced R Hs) as [[Hr _]|[_ H]]; [|exact H].
      rewrite Hb in Hr. discriminate.
    Qed.

    Lemma mprotect_expose_intro_some : ltac2:(tb__ "0|1|
S2S8dS1dA1M0G0S8bVi;Vm;R1A3LR;A2").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hwrap.
      destruct (mprotect_budget_ok m addr n) eqn:Hb.
      - eexists. exact (mprotect_expose_intro_ok Hb).
      - eexists. exact (mprotect_expose_intro_fail Hb).
    Qed.
  End Expose.

  Section Noop.
    Hypothesis Hna : ltac2:(tb__ "0|0|
S0SaS48S39Vh;A1Vaddr;Vn;A3S10A3").
    Hypothesis Hmp : ltac2:(tb__ "0|0|
S0SaS48S2eVh;A1Vaddr;Vn;A3SdA3").
    Hypothesis Hrf : ltac2:(tb__ "0|0|
S0SaS3fS39Vh;A1Vaddr;Vn;A3SdA3").

    Lemma mprotect_noop_inv : ltac2:(tb__ "0|0|
S8dS1dA1S8bVi;Vm;R1A3S9eR2S19Q40Z0A2Vm;S7S1eA1A4F_;FR;").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hrf Hwrap.
      intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
      - rewrite mprotect_gates, Hna, Hmp, Hrf in Hs. cbn [andb] in Hs.
        destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate].
        destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
        destruct ci; [|discriminate].
        destruct (w_is0 r) eqn:G; [|discriminate]. apply w_is0_spec in G. subst.
        inversion Hs; subst. reflexivity.
      - exfalso. specialize (Hs probe_eff). rewrite mprotect_gates, Hna, Hmp, Hrf in Hs.
        unfold probe_eff in Hs. cbn in Hs. discriminate.
    Qed.

    Lemma mprotect_noop_intro_ss : ltac2:(tb__ "0|3|
S8bVi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6Vm;S7S1eA1A4A3").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hrf Hwrap.
      apply check_spec_ok. rewrite mprotect_gates, Hna, Hmp, Hrf. reflexivity.
    Qed.

    Lemma mprotect_noop_intro : ltac2:(tb__ "0|3|
S106Vi;Vm;S8cS1dS23S19Q40M0Z0A2S7S8S17G0A1M1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6Vm;S7S1eA1A4A3").
    Proof using Halign Hlen Hmp Hna Hno Hprot Hrf Hwrap.
      intros. split; [eapply mprotect_noop_intro_ss; eassumption|].
      intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_nonenomem_mprotect; [assumption|]. cbn [eff_ret]. exact ret_zero_not_enomem.
    Qed.
  End Noop.
End Mprotect.

Definition brk_eff (h : VmMaps) (req r : word) : SyscallEffect := ltac2:(tb__ "0|2|
S23Vr;S7S8S17Q40A1M0S9S17Q8A1A1A2A1Se1Vreq;Vr;S2bVh;A1M1A3SdeVr;G1A2S7S22A1S7S8G0ScA2A1A6").

Section Brk.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 214%Z.
  Let req := in_arg i 0.
  Let h := m_vmmaps m.

  Lemma brk_check : ltac2:(tb__ "0|0|
S1dS0S80Sb7Vi;R1Vm;A3SffVreq;R1Vm;A3A3Feff;").
  Proof using Hno. intros eff. dispatch Hno. reflexivity. Qed.

  Lemma brk_inv : ltac2:(tb__ "0|2|
S8dS1dA1M0S8bVi;Vm;R1A3S2S17Q40A1M1G1S1S0SaSd7Vm;Vreq;R1A3SdA3S0G0R3S8cS1dSa5Vh;Vreq;R1A3Sd0Vm;Vreq;R1A3S7S1eA1A4A3A2Lr;A2F_;FR;").
  Proof using Hno.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite brk_check in Hs. unfold check_brk in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:G; [|discriminate] end.
      apply andb_true_iff in G as [G G3]. apply andb_true_iff in G as [G1 G2].
      apply listNN_eqb_eq in G2. apply listNN_eqb_eq in G3. subst.
      inversion Hs; subst. exists r. split; [exact G1|reflexivity].
    - exfalso. specialize (Hs probe_eff). rewrite brk_check in Hs. unfold check_brk, probe_eff in Hs.
      match type of Hs with (if ?c then _ else _) = _ => destruct c; discriminate end.
  Qed.

  Lemma brk_intro : ltac2:(tb__ "0|0|
S17Q40A1S0SaSd7Vm;Vreq;R1A3SdA3S8bVi;Vm;S8cS1dSa5Vh;Vreq;R2A3Sd0Vm;Vreq;R2A3S7S1eA1A4A3F_;Fr;").
  Proof using Hno.
    intros r Hr. apply check_spec_ok. rewrite brk_check. unfold check_brk, brk_eff.
    unfold h in *. rewrite Hr, !(proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.
End Brk.

Lemma brk_r_ok_query : ltac2:(tb__ "0|2|
S1fS17Q40M0A1M1S4S0SaSd7R2S19G0Z0A2R1A3SdA3S0G1R1S2bS20R2A1A1A3A2Fr;Fm;").
Proof.
  intros m r. unfold brk_r_ok. change (w_is0 (Z_to_bv 64 0)) with true. cbn [orb].
  apply bv_eqb_eq.
Qed.

Lemma brk_page_range_empty : ltac2:(tb__ "0|2|
S7fS0S9S8S17Q40A1M0G0A2M1A1Se4R1R1A2S7G1A1A3Flo;").
Proof. intros lo. unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity. Qed.

Lemma brk_zeros_same : ltac2:(tb__ "0|2|
S17Q40A1M0G0S0S9S8G0G0A2M1A1Se1R2R1R1A3S7G1A1A3Fb;Freq;").
Proof.
  intros req b. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_unmaps_same : ltac2:(tb__ "0|2|
S17Q40A1M0S0S9S8G0G0A2M1A1SdeR1R1A2S7G1A1A3Fb;").
Proof.
  intros b. unfold brk_unmaps. rewrite brk_page_range_empty. destruct (0 <? bv_unsigned b)%Z; reflexivity.
Qed.

Lemma brk_grants_same : ltac2:(tb__ "0|2|
S17Q40A1M0G0S0S9S8G0G0A2M1A1Se3R2R1R1A3S7G1A1A3Fb;Freq;").
Proof.
  intros req b. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_model_next_same : ltac2:(tb__ "0|1|
S29S17Q40A1S0S29Sd6R2R1S2bR2A1M0A3S43S36R2A1S2eR2A1S39R2A1S3aR2A1G0S44R2A1S4aR2A1S26R2A1A8A3Freq;Fh;").
Proof.
  intros h req. unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_same, brk_unmaps_same. reflexivity.
Qed.

Lemma brk_same_model : ltac2:(tb__ "0|0|
S1fS17Q40A1S0S1fSd0R2R1S2bS20R2A1A1A3R2A3Freq;Fm;").
Proof.
  intros m req. unfold with_brk_next. rewrite brk_unmaps_same. cbn [forget_vm_ranges].
  rewrite brk_model_next_same. apply with_vmmaps_eta.
Qed.

Lemma brk_eff_same : ltac2:(tb__ "0|3|
S29S17Q40A1M0S0S1dSa5R2R1S2bR2A1M1A3S23G1S7S8G0S9S17Q8A1A1A2A1S7S8G0G0A2A1M2G2S7S22A1S7S8G0ScA2A1A6A3Freq;Fh;").
Proof. intros h req. unfold brk_eff. rewrite brk_zeros_same, brk_unmaps_same. reflexivity. Qed.

Lemma brk_query_inv : ltac2:(tb__ "0|1|
S30S1fS8dS1dA1S0S7fS18Q40M0S42R3A1A2Zd6A3S0S17G0A1S21R4U0A2S19G0Z0A2A3S8bR5R4R3A3S9eR4S2bS20R5A1A1R5S7S1eA1A4F_;F_;F_;FR;Fm;Fi;").
Proof.
  intros i m R Hno Hq Hs. destruct (brk_inv i m Hno R Hs) as (r & Hr & ->).
  rewrite Hq in Hr |- *. apply brk_r_ok_query in Hr. subst r.
  rewrite brk_eff_same, brk_same_model. reflexivity.
Qed.

Lemma brk_query_intro_ss : ltac2:(tb__ "0|3|
S30S1fS0S7fS18Q40M0S42R2A1A2Zd6A3S0S17G0A1M1S21R3U0A2S19G0Z0A2A3S8bR4R3S8cS1dS23S2bS20R3A1A1S7S8G1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6R3S7S1eA1A4A3F_;F_;Fm;Fi;").
Proof.
  intros i m Hno Hq.
  pose proof (brk_intro i m Hno (vm_brk (m_vmmaps m))) as H. rewrite Hq in H.
  rewrite brk_eff_same, brk_same_model in H. apply H. apply brk_r_ok_query. reflexivity.
Qed.

Lemma brk_query_intro : ltac2:(tb__ "0|3|
S30S1fS0S7fS18Q40M0S42R2A1A2Zd6A3S0S17G0A1M1S21R3U0A2S19G0Z0A2A3S106R4R3S8cS1dS23S2bS20R3A1A1S7S8G1S9S17Q8A1A1A2A1S7S8G1G1A2A1M2G2S7S22A1S7S8G1ScA2A1A6R3S7S1eA1A4A3F_;F_;Fm;Fi;").
Proof.
  intros. split; [eapply brk_query_intro_ss; eassumption|].
  intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_brk_query; assumption.
Qed.

Lemma brk_r_ok_grow : ltac2:(tb__ "0|2|
S1fS17Q40M0A1M1G1S20R3A1S29S8fS18G0S3aR1A1A2S18G0S2bR1A1A2A2S92S18G0S2bR2A1A2S18G0R4A2A2S4S0SaSd7R6R5R4A3SdA3S3S1S0G1R4R5A3S0SaSddR6R5R5A3SdA3A2S0G1R4S2bR3A1A3A2A2F_;F_;Th;Fr;Freq;Fm;").
Proof.
  intros m req r h Hsb Hlt. unfold brk_r_ok, min_brk. subst h.
  pose proof (word_unsigned_range (vm_brk (m_vmmaps m))) as Hb.
  assert (E0 : w_is0 req = false) by (apply w_is0_false; lia).
  rewrite E0. cbn [orb].
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_start_brk (m_vmmaps m)))) ltac:(lia)).
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))) ltac:(lia)).
  split.
  - intros H. apply andb_true_iff in H as [H1 H2]. apply orb_true_iff in H1 as [H1|H1];
      apply bv_eqb_eq in H1; subst; auto.
  - intros [[-> Hg] | ->].
    + rewrite bv_eqb_refl, Hg. reflexivity.
    + rewrite bv_eqb_refl, orb_true_r. cbn [andb].
      unfold brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_unmaps_grow : ltac2:(tb__ "0|3|
S17Q40M0A1M1G1S8fS18G0R1A2S18G0R2A2A2S0S9S8G1G1A2M2A1SdeR3R2A2S7G2A1A3F_;Fold;Fr;").
Proof.
  intros r old Hle. unfold brk_unmaps.
  destruct (0 <? bv_unsigned old)%Z; [|reflexivity].
  unfold brk_page_range.
  rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity|].
  apply page_round_up_Z_mono. exact Hle.
Qed.

Lemma with_brk_next_grow : ltac2:(tb__ "0|2|
S1fS17Q40M0A1M1G1S8fS18G0S2bS20R3A1A1A2S18G0R1A2A2S0S1fSd0R4R3R2A3S3cSd6S20R4A1R3R2A3R4A2A3F_;Fr;Freq;Fm;").
Proof.
  intros m req r Hle. unfold with_brk_next. rewrite (brk_unmaps_grow _ _ Hle). reflexivity.
Qed.

Lemma brk_grow_inv : ltac2:(tb__ "0|7|
S30S1fS8dS1dA1M0S0S7fS18Q40M1S42R3A1A2Zd6A3S8fS18G1S3aS20R3A1M2A1A2S18G1S2bG2A1A2A2S92S18G1S2bS20R4A1A1A2S18G1S21R5U0M3A2A2A2S8bR6R5R4A3S3S1S0SaSddR6S21R7G3A2M4G4A3SdA3S0G0R5S8cS1dSa5S20R6A1M5G4G4A3S3cSd6G5G4G4A3R6A2S7S1eA1M6A4A3A2S9eR5S2bG5A1R6G6A4A2F_;F_;F_;F_;FR;Fm;Fi;").
Proof.
  intros i m R Hno Hsb Hlt Hs. destruct (brk_inv i m Hno R Hs) as (r & Hr & ->).
  apply (brk_r_ok_grow _ _ _ Hsb Hlt) in Hr. destruct Hr as [[-> Hg] | ->].
  - left. rewrite with_brk_next_grow by lia. auto.
  - right. rewrite brk_eff_same, brk_same_model. reflexivity.
Qed.

Lemma brk_grow_intro_ok_ss : ltac2:(tb__ "0|6|
S30S1fS0S7fS18Q40M0S42R2A1A2Zd6A3S8fS18G0S3aS20R2A1M1A1A2S18G0S2bG1A1A2A2S92S18G0S2bS20R3A1A1A2S18G0S21R4U0M2A2A2A2S0SaSddR4S21R5G2A2M3G3A3SdA3S8bR6R5S8cS1dSa5S20R5A1M4S21R6G2A2M5G5A3S3cSd6G4G5G5A3R5A2S7S1eA1A4A3F_;F_;F_;F_;Fm;Fi;").
Proof.
  intros i m Hno Hsb Hlt Hg.
  rewrite <- with_brk_next_grow by lia. apply brk_intro; [exact Hno|].
  apply (brk_r_ok_grow _ _ _ Hsb Hlt). left. auto.
Qed.

Lemma brk_grow_intro_ok : ltac2:(tb__ "0|6|
S30S1fS0S7fS18Q40M0S42R2A1A2Zd6A3S8fS18G0S3aS20R2A1M1A1A2S18G0S2bG1A1A2A2S92S18G0S2bS20R3A1A1A2S18G0S21R4U0M2A2A2A2S0SaSddR4S21R5G2A2M3G3A3SdA3S106R6R5S8cS1dSa5S20R5A1M4S21R6G2A2M5G5A3S3cSd6G4G5G5A3R5A2S7S1eA1A4A3F_;F_;F_;F_;Fm;Fi;").
Proof.
  intros. split; [eapply brk_grow_intro_ok_ss; eassumption|].
  intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_brk_moved; [assumption|]. cbn [eff_ret brk_eff]. intro E. match goal with H : (bv_unsigned (vm_brk _) < bv_unsigned (in_arg _ 0))%Z |- _ => rewrite E in H; lia end.
Qed.

Lemma brk_grow_intro_fail : ltac2:(tb__ "0|4|
S30S1fS0S7fS18Q40M0S42R2A1A2Zd6A3S8fS18G0S3aS20R2A1M1A1A2S18G0S2bG1A1A2A2S92S18G0S2bS20R3A1A1A2S18G0S21R4U0A2A2A2S8bR5R4S8cS1dS23S2bS20R4A1A1S7S8S17G0A1M2S9S17Q8A1A1A2A1S7S8G2G2A2A1M3G3S7S22A1S7S8G2ScA2A1A6R4S7S1eA1A4A3F_;F_;F_;Fm;Fi;").
Proof.
  intros i m Hno Hsb Hlt.
  pose proof (brk_intro i m Hno (vm_brk (m_vmmaps m))) as H.
  rewrite brk_eff_same, brk_same_model in H. apply H.
  apply (brk_r_ok_grow _ _ _ Hsb Hlt). right. reflexivity.
Qed.

Lemma brk_grow_intro_fail_ns : forall i m,
  bv_unsigned (in_sysno i) = 214%Z ->
  (bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned (vm_brk (m_vmmaps m)))%Z ->
  (bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned (in_arg i 0))%Z ->
  brk_grow_ok m (in_arg i 0) (in_arg i 0) = false ->
  syscall_spec_ns i m (Ok (mkEffect (vm_brk (m_vmmaps m)) [] []) m []).
Proof.
  intros i m Hno Hsb Hlt Hg. split; [exact (brk_grow_intro_fail i m Hno Hsb Hlt)|].
  intros eff m' evs E _. injection E; intros ? ? ?; subst eff m' evs.
  apply ns_all_same_ret. intros eff' m1 evs1 Hs.
  destruct (brk_grow_inv i m _ Hno Hsb Hlt Hs) as [(Hg' & _) | E']; [congruence|].
  injection E'; intros ? ? ?; subst eff'. reflexivity.
Qed.

Lemma page_round_up_Z_id : ltac2:(tb__ "0|0|
S7fS0S7fS93R1S32A2Z0A3S0S7fS79R2A1R2A3F_;Fz;").
Proof.
  intros z Hz. unfold page_round_up_Z, page_size in *.
  rewrite Z.mod_divide in Hz by lia. destruct Hz as [k ->].
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096)%Z with 0%Z. lia.
Qed.

Lemma brk_eff_grow_aligned : ltac2:(tb__ "0|7|
S29S17Q40M0A1M1S0S7fS93S18G0S2bR2A1A2S32A2Z0M2A3S0S7fS93S18G0R2A2S32A2G2A3S1S92G2S18G0S2bR4A1A2M3A2S92G3S18G0R3A2A2A2S0S1dSa5R5R4R4A3S23R4S7S8G1S9S17Q8A1A1A2A1SbS8G1G1A2M4SfG1G1S2bR5A1M5S1cG0R4G5A3A4S7G4A1M6A3G6S7S22A1S7S8G1ScA2A1A6A3F_;F_;F_;Freq;Fh;").
Proof.
  intros h req Ho Hr Hlt. unfold brk_eff.
  rewrite (brk_unmaps_grow req (vm_brk h)) by lia.
  unfold brk_zeros, brk_is_grow.
  rewrite (w_is0_pos req) by lia. cbn [negb andb].
  rewrite (proj2 (Z.ltb_lt _ _) (proj1 Hlt)), (proj2 (Z.ltb_lt _ _) (proj2 Hlt)). cbn [andb].
  unfold brk_page_range. rewrite (page_round_up_Z_id _ Ho), (page_round_up_Z_id _ Hr).
  rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hlt)).
  rewrite Z_to_bv_bv_unsigned. do 3 f_equal.
Qed.

Lemma m_vmmaps_forget_vm_ranges : ltac2:(tb__ "0|1|
S9S8S17Q40A1M0G0A2A1S1fS0S29S20Se5R2R1A2A1S20R1A1A3Fm;Franges;").
Proof. induction ranges as [|[a n] r IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.

Lemma vm_init_sp_with_brk_next : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S0G0S26S20Sd0R3R2R1A3A1A1S26S20R3A1A1A3Fr;Freq;Fm;").
Proof. intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges. reflexivity. Qed.

Lemma vm_init_sp_mprotect_model_next : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S0G0S26S20SebR3R2R1A3A1A1S26S20R3A1A1A3Fn;Faddr;Fm;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_vm_forget_range : ltac2:(tb__ "0|0|
S7fS7fS1fS0S17Q40A1S26S20S40R3R2R1A3A1A1S26S20R1A1A1A3Fm;Fhi;Flo;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_exit_model : ltac2:(tb__ "0|0|
S30S1fS0S17Q40A1S26S20Sa2R2R1A2A1A1S26S20R1A1A1A3Fm;Fi;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_with_fds : ltac2:(tb__ "0|1|
S9S8S17Q40A1M0S24A2A1S1fS0G0S26S20S38R2R1A2A1A1S26S20R1A1A1A3Fm;Ff;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_with_stdin : ltac2:(tb__ "0|0|
S4fS1fS0S17Q40A1S26S20S55R2R1A2A1A1S26S20R1A1A1A3Fm;Fv;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_with_fs : ltac2:(tb__ "0|0|
ScaS1fS0S17Q40A1S26S20S54R2R1A2A1A1S26S20R1A1A1A3Fm;Fv;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_with_tid : ltac2:(tb__ "0|1|
S17Q40A1M0S1fS0G0S26S20S4dR2R1A2A1A1S26S20R1A1A1A3Fm;Fv;").
Proof. reflexivity. Qed.

Lemma vm_init_sp_with_halted : ltac2:(tb__ "0|1|
S17Q40A1M0S1fS0G0S26S20S51R2R1A2A1A1S26S20R1A1A1A3Fm;Fv;").
Proof. reflexivity. Qed.

Lemma init_sp_ok_mmap_rw_model : ltac2:(tb__ "0|1|
S17Q40A1M0S1fG0G0S9dS20R3A1A1S9dS20Sa4R5R4R3R2A4A1A1F_;Fa;Flen;Fm;Fflags;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_mmap_rw_model | assumption]. Qed.
Lemma init_sp_ok_mmap_none_model : ltac2:(tb__ "0|1|
S17Q40A1M0S1fG0G0S9dS20R3A1A1S9dS20Sa3R5R4R3R2A4A1A1F_;Fa;Flen;Fm;Fflags;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_mmap_none_model | assumption]. Qed.
Lemma init_sp_ok_mmap_fixed_ok_model : ltac2:(tb__ "0|1|
S17Q40A1M0S1fG0G0S9dS20R3A1A1S9dS20Sa6R5R4R3R2A4A1A1F_;Fn;Faddr;Fm;Fflags;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_mmap_fixed_ok_model | assumption]. Qed.
Lemma init_sp_ok_mmap_fixed_dead_model : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S9dS20R3A1A1S9dS20SacR4R3R2A3A1A1F_;Fn;Faddr;Fm;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_mmap_fixed_dead_model | assumption]. Qed.
Lemma init_sp_ok_munmap_model : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S9dS20R3A1A1S9dS20SabR4R3R2A3A1A1F_;Fn;Faddr;Fm;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_munmap_model | assumption]. Qed.
Lemma init_sp_ok_with_brk_next : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S9dS20R3A1A1S9dS20Sd0R4R3R2A3A1A1F_;Fr;Freq;Fm;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_with_brk_next | assumption]. Qed.
Lemma init_sp_ok_mprotect_model_next : ltac2:(tb__ "0|1|
S1fS17Q40A1M0G0S9dS20R3A1A1S9dS20SebR4R3R2A3A1A1F_;Fn;Faddr;Fm;").
Proof. intros. eapply init_sp_ok_same; [apply vm_init_sp_mprotect_model_next | assumption]. Qed.
Lemma init_sp_ok_with_fds : ltac2:(tb__ "0|0|
S9S8S17Q40A1S24A2A1S1fS9dS20R1A1A1S9dS20S38R3R2A2A1A1F_;Fm;Ff;").
Proof. intros. exact H. Qed.
Lemma init_sp_ok_with_stdin : ltac2:(tb__ "0|0|
S4fS1fS9dS20R1A1A1S9dS20S55R3R2A2A1A1F_;Fm;Fv;").
Proof. intros. exact H. Qed.
Lemma init_sp_ok_with_fs : ltac2:(tb__ "0|0|
ScaS1fS9dS20R1A1A1S9dS20S54R3R2A2A1A1F_;Fm;Fv;").
Proof. intros. exact H. Qed.
Lemma init_sp_ok_with_tid : ltac2:(tb__ "0|0|
S17Q40A1S1fS9dS20R1A1A1S9dS20S4dR3R2A2A1A1F_;Fm;Fv;").
Proof. intros. exact H. Qed.
Lemma init_sp_ok_with_halted : ltac2:(tb__ "0|0|
S17Q40A1S1fS9dS20R1A1A1S9dS20S51R3R2A2A1A1F_;Fm;Fv;").
Proof. intros. exact H. Qed.
Lemma init_sp_ok_exit_model : ltac2:(tb__ "0|0|
S30S1fS9dS20R1A1A1S9dS20Sa2R3R2A2A1A1F_;Fm;Fi;").
Proof. intros. exact H. Qed.
