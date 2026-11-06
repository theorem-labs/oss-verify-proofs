(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
Lemma in_a0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = areg ms 10.
Proof. reflexivity. Qed.

Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
  forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.

Definition iovec_bytes (iovs : list (word * word)) : list byte :=
  flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.

Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
  snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

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
End AC_1.

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
Section AC_2. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition kmmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
               ((a, n) :: vm_maps (m_vmmaps m))
               (vm_noaccess (m_vmmaps m))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Definition knoaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Definition kmunmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) addr)
               (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr)
                  (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Definition kmprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Definition kfixna_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).
Definition kfixlost_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition kbrk_grow_model (d : Z) (m : Model) : Model :=
  let h := m_vmmaps m in let b := vm_brk h in
  with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                 (vm_noaccess h) (vm_start_brk h)
                 (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.

Definition kgrant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_ceiling)%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.
Definition kgrant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_ceiling)%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Definition kbrk_grow_ok (m : Model) (req r : word) : bool :=
  let h := m_vmmaps m in
  if Z.ltb 0 (bv_unsigned (vm_brk h))
     && Z.ltb (bv_unsigned (vm_brk h)) (bv_unsigned r)
  then let lo := page_round_up_Z (bv_unsigned (vm_brk h)) in
       let hi := page_round_up_Z (bv_unsigned r) in
       (if Z.ltb lo hi
        then Z.leb hi alloc_ceiling
             && region_free (vm_reserved h ++ vm_maps h)
                            (Z_to_bv 64 lo) (Z_to_bv 64 (hi + page_size - lo))
        else true)
       && Z.leb (vm_backing_used m + bv_unsigned (r - vm_brk h)) (vm_limit h)
  else true.

Lemma kbrk_grow_ok_spec : forall m req r,
  alloc_top (m_vmmaps m) = alloc_ceiling -> kbrk_grow_ok m req r = Mmap.brk_grow_ok m req r.
Proof. intros m req r E. unfold kbrk_grow_ok, Mmap.brk_grow_ok, Mmap.brk_budget_ok. rewrite E. reflexivity. Qed.

Definition MAP_ANON_PRIV : Z := 34.
Definition MAP_ANON_PRIV_FIXED : Z := 50.
Definition PROT_RW_Z : Z := 3.

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  evs = [] /\
  match n with
  | NBrk req =>
      let h := m_vmmaps mo in let b := vm_brk h in
      if (req =? 0)%Z then eff = eff0 b /\ mo' = mo
      else
        (eff = eff0 b /\ mo' = mo)
        \/ (kbrk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true
            /\ eff = mkEffect (Z_to_bv 64 req) [] [(b, Z_to_bv 64 (req - bv_unsigned b))]
            /\ mo' = kbrk_grow_model (req - bv_unsigned b) mo)
  | NMmap addr len prot flags =>
      let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
      if ((flags =? MAP_ANON_PRIV) && (prot =? PROT_RW_Z))%Z then
        (exists e, In e mmap_errnos /\ eff = efferr e /\ mo' = mo)
        \/ (exists a, kgrant_ok (Z_to_bv 64 addr) mo a nZ = true
                      /\ eff = mkEffect a [] [(a, n)] /\ mo' = kmmap_model a n mo)
      else if ((flags =? MAP_ANON_PRIV) && (prot =? 0))%Z then
        (exists e, In e mmap_errnos /\ eff = efferr e /\ mo' = mo)
        \/ (exists a, kgrant_ok_na (Z_to_bv 64 addr) mo a nZ = true
                      /\ eff = mkEffectU a [] [] [(a, n)] [] [] /\ mo' = knoaccess_model a n mo)
      else if ((flags =? MAP_ANON_PRIV_FIXED) && (prot =? 0))%Z then
        let aw := Z_to_bv 64 addr in
        (exists e, In e mmap_errnos /\ eff = efferr e /\ mo' = mo)
        \/ (eff = mkEffectU aw [] [] [(aw, n)] [] [] /\ mo' = kfixna_model aw n mo)
        \/ (exists e, In e mmap_errnos /\ eff = mkEffectU (errno_ret e) [] [] [(aw, n)] [] [] /\ mo' = kfixlost_model aw n mo)
      else False
  | NMunmap addr len =>
      let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (page_round_up_Z len) in
      eff = mkEffectU (Z_to_bv 64 0) [] [] [(aw, n)] [] [] /\ mo' = kmunmap_model aw n mo
  | NMprotect addr len prot =>
      let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (page_round_up_Z len) in
      (exists e, In e mprotect_errnos /\ eff = efferr e /\ mo' = mo)
      \/ (mprotect_budget_ok mo aw n = true /\ eff = mkEffect (Z_to_bv 64 0) [] [(aw, n)] /\ mo' = kmprotect_model aw n mo)
  | _ => False
  end.

Definition nrefusal (n : node) (mo : Model) (eff : resp) : bool :=
  match n with
  | NBrk req => brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff)
  | NMmap _ _ _ _ => bv_eqb (eff_ret eff) (errno_ret ENOMEM)
  | NMprotect _ _ _ => ret_in_errnos mprotect_errnos (eff_ret eff)
  | _ => false
  end.

Definition nstep_cfg (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo eff mo' evs
  /\ (nrefusal n mo eff = true ->
      forall eff' mo'' evs', nstep n mo eff' mo'' evs' -> nrefusal n mo eff' = true).

Lemma nstep_cfg_sub : forall n mo eff mo' evs, nstep_cfg n mo eff mo' evs -> nstep n mo eff mo' evs.
Proof. intros n mo eff mo' evs [H _]. exact H. Qed.

Lemma nstep_cfg_of_nonref : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> nrefusal n mo eff = false -> nstep_cfg n mo eff mo' evs.
Proof. intros n mo eff mo' evs H Hn. split; [exact H |]. intros Hr. congruence. Qed.

Lemma nstep_cfg_exists : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> exists eff1 mo1 evs1, nstep_cfg n mo eff1 mo1 evs1.
Proof.
  intros n mo eff mo' evs H.
  destruct (Classical_Prop.classic (exists eff1 mo1 evs1, nstep n mo eff1 mo1 evs1 /\ nrefusal n mo eff1 = false))
    as [(eff1 & mo1 & evs1 & H1 & Hr1) | Hno].
  - exists eff1, mo1, evs1. apply nstep_cfg_of_nonref; assumption.
  - exists eff, mo', evs. split; [exact H |]. intros _ eff' mo'' evs' H'.
    destruct (nrefusal n mo eff') eqn:E; [reflexivity |].
    exfalso. apply Hno. exists eff', mo'', evs'. auto.
Qed.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

Definition minv (mo : Model) : Prop :=
  m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

Definition nsafe (n : node) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  match n with
  | NBrk req =>
      req = 0
      \/ (let b := bv_unsigned (vm_brk h) in
          b mod page_size = 0 /\ req mod page_size = 0 /\ 0 < b /\ b < req < 2 ^ 64
          /\ bv_unsigned (vm_start_brk h) <= req)
  | NMmap addr len prot flags =>
      0 < len < 2 ^ 64 /\
      ((flags = MAP_ANON_PRIV /\ prot = PROT_RW_Z /\ addr = 0)
       \/ (flags = MAP_ANON_PRIV /\ prot = 0 /\ addr = 0)
       \/ (flags = MAP_ANON_PRIV_FIXED /\ prot = 0
           /\ addr mod page_size = 0 /\ 0 < addr /\ addr + page_round_up_Z len <= alloc_ceiling
           /\ region_free (vm_reserved h) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
           /\ map_contains (vm_maps h) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true))
  | NMunmap addr len =>
      addr mod page_size = 0 /\ 0 < len /\ 0 <= addr /\ addr + page_round_up_Z len <= TASK_SIZE
      /\ map_has (vm_maps h) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
  | NMprotect addr len prot =>
      prot = PROT_RW_Z /\ addr mod page_size = 0 /\ 0 < len /\ 0 <= addr /\ addr + page_round_up_Z len < 2 ^ 64
      /\ map_contains (vm_noaccess h) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
      /\ map_contains (vm_maps h) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
  | _ => False
  end.

Definition vm_only (m m' : Model) : Prop :=
  m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\
  m_lim m' = m_lim m /\ m_time m' = m_time m.

Lemma vm_only_fs : forall m m', vm_only m m' -> m_fs m' = m_fs m.
Proof. intros m m' (A&B&C&D&E&F). unfold m_fs. rewrite C. reflexivity. Qed.
Lemma vm_only_fds : forall m m', vm_only m m' -> m_fds m' = m_fds m.
Proof. intros m m' (A&B&C&D&E&F). unfold m_fds. rewrite A. reflexivity. Qed.

End AC_2.
