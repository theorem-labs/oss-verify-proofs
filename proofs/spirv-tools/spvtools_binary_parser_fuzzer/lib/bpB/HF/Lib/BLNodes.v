(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.

From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BExec BITree.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.

Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
  forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.

Definition iovec_bytes (iovs : list (word * word)) : list byte :=
  flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.

Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
  snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

Inductive node : Type :=
| NWrite (fd : Z) (bs : list byte)
| NWritev (fd : Z) (bufs : list (list byte))
| NOpen (path : list byte)
| NRead (fd : Z) (buf : Z) (count : Z)
| NClose (fd : Z)
| NIoctl (fd : Z) (req : Z)
| NSetTid
| NExit (code : Z)
| NBrk (req : Z)
| NMmap (addr len prot flags : Z)
| NMunmap (addr len : Z)
| NMprotect (addr len prot : Z).

Definition pure_input (no : Z) (args : list word) : SyscallInput :=
  mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).

Definition node_input (n : node) : option SyscallInput :=
  match n with
  | NBrk req => Some (pure_input 214 [Z_to_bv 64 req])
  | NMmap addr len prot flags =>
      Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
  | NMunmap addr len => Some (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])
  | NMprotect addr len prot => Some (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
  | _ => None
  end.

Section AtNode.
Variable segs : list Segment.

Definition at_node (n : node) (ms : machine_state) : Prop :=
  match n with
  | NWrite fd bs =>
      ms_svc_pending ms = Some (Z_to_bv 64 64) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bs)) /\
      Z.of_nat (length bs) < 2^64 /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (length bufs <= 1024)%nat /\
      Z.of_nat (length (concat bufs)) < 2^63 /\
      ms_rom ms = seg_rom segs /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) (O_CLOEXEC + O_LARGEFILE) = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      0 <= count /\
      wr_at segs (ms_mem ms) buf count
  | NClose fd =>
      ms_svc_pending ms = Some (Z_to_bv 64 57) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd
  | NIoctl fd req =>
      ms_svc_pending ms = Some (Z_to_bv 64 29) /\
      0 <= fd <= 2 /\ req = 21523 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 req
  | NSetTid =>
      ms_svc_pending ms = Some (Z_to_bv 64 96)
  | NExit code =>
      (ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94)) /\
      areg ms 10 = Z_to_bv 64 code
  | NBrk req =>
      ms_svc_pending ms = Some (Z_to_bv 64 214) /\
      areg ms 10 = Z_to_bv 64 req
  | NMmap addr len prot flags =>
      ms_svc_pending ms = Some (Z_to_bv 64 222) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
      areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
      areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
  | NMunmap addr len =>
      ms_svc_pending ms = Some (Z_to_bv 64 215) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
  | NMprotect addr len prot =>
      ms_svc_pending ms = Some (Z_to_bv 64 226) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot
  end.

End AtNode.

Ltac at_node_red :=
  cbn [at_node]; unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac split_spine :=
  lazymatch goal with
  | |- _ /\ _ => split; [|split_spine]
  | |- _ => idtac
  end.

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Section NStep.
Context {SC : StepCfg}.
Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWrite fd bs =>
      eff = eff0 (Z_to_bv 64 (Z.of_nat (length bs))) /\ mo' = mo /\
      evs = map (WriteEv (Z_to_bv 64 fd)) bs
  | NWritev fd bufs =>
      eff = eff0 (Z_to_bv 64 (Z.of_nat (length (concat bufs)))) /\ mo' = mo /\
      evs = map (WriteEv (Z_to_bv 64 fd)) (concat bufs)
  | NOpen path =>
      evs = [] /\
      if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => eff = efferr ENOENT /\ mo' = mo
           | _ => if path_eqb path dot_path then open_result mo FdDir eff mo'
                  else match fs_lookup (m_fs mo) path with
                       | None => eff = efferr ENOENT /\ mo' = mo
                       | Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
                       end
           end
  | NRead fd buf count =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some FdDir => eff = efferr EISDIR /\ mo' = mo
      | Some (FdFile p off) =>
          match fs_lookup (m_fs mo) p with
          | None => False
          | Some data =>
              let bs := file_read data off (Z_to_bv 64 count) in
              eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
          end
      | Some (FdChannel _) | Some (FdFileW _ _) | Some (FdSocket _) | Some (FdPipe _ _)
      | Some (FdFileA _ _) | Some (FdFileRW _ _) | Some (FdDevNull _ _) | Some FdUrandom => False
      end
  | NClose fd =>
      evs = [] /\ 3 <= fd < 2^32 /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some _ => eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
      end
  | NIoctl fd req => evs = [] /\ eff = efferr ENOTTY /\ mo' = mo
  | NSetTid =>
      evs = [] /\ exists t, eff = eff0 t /\
      match m_tid mo with
      | Some t0 => t = t0 /\ mo' = mo
      | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
      end
  | NExit _ => False
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>

      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg the_scfg i mo eff
      | None => False
      end
  end.
End NStep.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

Definition minv (mo : Model) : Prop :=
  m_vm_lazy mo = [] /\
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
  (forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
  (forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileW p off)) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE).

Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ) then false
    else
      let n := Z_to_bv 64 nZ in
      map_has (vm_maps h) addr n || region_free (vm_reserved h ++ vm_maps h) addr n.

Definition mprotect_safe_b (addr len prot : word) (h : VmMaps) : bool :=
  if mprotect_grows_conflict_b prot then true
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
  else if w_is0 len then true
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
  else if mprotect_modeled_b prot then
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
    || (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n)
  else false.

Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  mmap_modeled_b prot flags off
  || mmap_noaccess_b prot flags off
  || (if w_is0 len then mmap_plain_anon_b flags
      else if mmap_fixed_noaccess_b prot flags off then
        let nZ := page_round_up_Z (bv_unsigned len) in
        if (two_pow_64 <=? bv_unsigned addr + nZ) then true
        else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
        else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
        else region_free (vm_reserved h) addr (Z_to_bv 64 nZ) && map_contains (vm_maps h) addr (Z_to_bv 64 nZ)
      else false).

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
  | NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
  | NMprotect addr len prot =>
      mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
  | _ => True
  end.

Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
  m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.
