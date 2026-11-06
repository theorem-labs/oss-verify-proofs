(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0h.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YK0p YP0n YP0o YM06.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma SR_openat_tmp_create : forall regs pc mem rom model p n Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
SR segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model))) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model p n Q Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hfree HA HB T HK.
apply (rz_conseq segs _ (t_alt2 T T)); [|apply t_alt2_idem].
apply (rz_openat_tmp_create segs regs pc mem rom model p n T T Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hfree).
- intros e He. exact (HA e He T HK).
- exact (HB T HK).
Qed.
Lemma SR_openat_tmp_create_full : forall regs pc mem rom model p n Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) <> None ->
(forall e, In e openat_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model p n Q Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hocc HA T HK.
apply (rz_openat_tmp_create_full segs regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hocc).
intros e He. exact (HA e He T HK).
Qed.
Lemma SR_ioctl_winsz : forall regs pc mem rom model fd e Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 29%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
(forall rd wr : bool, e <> FdUrandom) ->
cmd32 (getr regs 11) = TIOCGWINSZ ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model fd e Q Hh Hlz Hno Hfd H32 Hlk Hnd Hcmd HK0 T HK.
apply (rz_ioctl_winsz segs regs pc mem rom model fd e T Hh Hlz Hno Hfd H32 Hlk Hnd Hcmd). exact (HK0 T HK).
Qed.
Lemma SR_close : forall regs pc mem rom model fd e Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 57%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fd) model)) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model fd e Q Hh Hlz Hno Hfd H32 Hlk HK0 T HK.
apply (rz_close segs regs pc mem rom model fd e T Hh Hlz Hno Hfd H32 Hlk). exact (HK0 T HK).
Qed.
Lemma SR_writev_file2 : forall regs pc mem rom model fd p off data (b0 l0 b1 l1 : word) bs0 bs1 Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 2 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
access_okb (getr regs 11) 32 = true ->
access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
(1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT)%Z ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + (bv_unsigned l0 + bv_unsigned l1) <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
SR segs (mkCfg (mkst (regupd regs 10 (len_word (bs0 ++ bs1))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word (bs0 ++ bs1))))
(with_fs (fs_set (m_fs model) p (file_write data off (bs0 ++ bs1))) model))) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model fd p off data b0 l0 b1 l1 bs0 bs1 Q
Hh Hlz Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hfs Hpos Hgap HK0 T HK.
apply (rz_writev_file2 segs regs pc mem rom model fd p off data b0 l0 b1 l1 bs0 bs1 T
Hh Hlz Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hfs Hpos Hgap).
exact (HK0 T HK).
Qed.
Lemma SR_writev_file1 : forall regs pc mem rom model fd p off data (b0 l0 : word) bs0 Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 (bv_unsigned l0) = true ->
(1 <= bv_unsigned l0 <= MAX_RW_COUNT)%Z ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + bv_unsigned l0 <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
SR segs (mkCfg (mkst (regupd regs 10 (len_word bs0)) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs0)))
(with_fs (fs_set (m_fs model) p (file_write data off bs0)) model))) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model fd p off data b0 l0 bs0 Q
Hh Hlz Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hfs Hpos Hgap HK0 T HK.
apply (rz_writev_file1 segs regs pc mem rom model fd p off data b0 l0 bs0 T
Hh Hlz Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hfs Hpos Hgap).
exact (HK0 T HK).
Qed.
Lemma SR_unlink_tmp_present : forall regs pc mem rom model p n d Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fs_lookup (m_fs model) p = Some d ->
fd_names_path (m_fds model) p = false ->
(forall e, In e unlinkat_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fs (fs_remove (m_fs model) p) model)) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model p n d Q Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfs Hfdn HA HB T HK.
apply (rz_conseq segs _ (t_alt2 T T)); [|apply t_alt2_idem].
apply (rz_unlink_tmp_present segs regs pc mem rom model p n d T T Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfs Hfdn).
- intros e He. exact (HA e He T HK).
- exact (HB T HK).
Qed.
Lemma SR_unlink_tmp_absent : forall regs pc mem rom model p n Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fs_lookup (m_fs model) p = None ->
fd_names_path (m_fds model) p = false ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom) model) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model p n Q Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfs Hfdn HK0 T HK.
apply (rz_unlink_tmp_absent segs regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfs Hfdn). exact (HK0 T HK).
Qed.
Lemma SR_unlink_tmp_isdir : forall regs pc mem rom model p n Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = true ->
fd_names_path (m_fds model) p = false ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model p n Q Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfdn HK0 T HK.
apply (rz_unlink_tmp_isdir segs regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfdn). exact (HK0 T HK).
Qed.
Lemma SR_openat_tmp_isdir : forall regs pc mem rom model p n Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = true ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model p n Q Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun HK0 T HK.
apply (rz_openat_tmp_isdir segs regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun). exact (HK0 T HK).
Qed.
Definition sink_path_bytes : path := map (Z_to_bv 8) [47; 116; 109; 112; 47; 111; 117; 116; 46; 103; 105; 102]%Z.
Definition sink_name_bytes : path := map (Z_to_bv 8) [111; 117; 116; 46; 103; 105; 102]%Z.
Lemma sink_path_facts :
path_eqb sink_path_bytes [] = false /\ path_strip_trailing_slashes sink_path_bytes = sink_path_bytes /\
path_has_slash sink_path_bytes = true /\ path_eqb sink_path_bytes localtime_path = false /\
path_eqb sink_path_bytes devnull_path = false /\ path_eqb sink_path_bytes urandom_path = false /\
tmp_name sink_path_bytes = Some sink_name_bytes /\ Nat.ltb NAME_MAX (length sink_name_bytes) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sink_path_key : tmp_key sink_name_bytes = sink_path_bytes.
Proof. vm_compute. reflexivity. Qed.
End a.
