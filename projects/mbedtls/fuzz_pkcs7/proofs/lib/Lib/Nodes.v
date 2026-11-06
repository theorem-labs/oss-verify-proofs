(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Exec ITree.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
Lemma in_a0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = areg ms 10.
Proof. reflexivity. Qed.
Lemma in_a1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = areg ms 11.
Proof. reflexivity. Qed.
Lemma in_a2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = areg ms 12.
Proof. reflexivity. Qed.
Lemma in_a3_si : forall segs ms x8, in_arg (sys_input segs ms x8) 3 = areg ms 13.
Proof. reflexivity. Qed.
Lemma in_a4_si : forall segs ms x8, in_arg (sys_input segs ms x8) 4 = areg ms 14.
Proof. reflexivity. Qed.
Lemma in_a5_si : forall segs ms x8, in_arg (sys_input segs ms x8) 5 = areg ms 15.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
  forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.










(* [comment removed for export] *)


(* [comment removed for export] *)
Definition iovec_bytes (iovs : list (word * word)) : list byte :=
  flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.





(* [comment removed for export] *)
Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros w. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Lemma wa_add : forall a (k : word), (wa a + k)%bv = wa (a + bv_unsigned k).
Proof. intros. rewrite <- (Z_to_bv_bv_unsigned k) at 1. unfold wa. apply lit_add_lit. Qed.

Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
  snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.




(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive node : Type :=
| NWrite (fd : Z) (bs : list byte)                 (* [comment removed for export] *)
| NWritev (fd : Z) (bufs : list (list byte))       (* [comment removed for export] *)
| NOpen (path : list byte)                         (* [comment removed for export] *)
| NRead (fd : Z) (buf : Z) (count : Z)             (* [comment removed for export] *)
| NClose (fd : Z)                                  (* [comment removed for export] *)
| NIoctl (fd : Z) (req : Z)                        (* [comment removed for export] *)
| NSetTid                                          (* [comment removed for export] *)
| NExit (code : Z)                                 (* [comment removed for export] *)
| NBrk (req : Z)                                   (* [comment removed for export] *)
| NMmap (addr len prot flags : Z)                  (* [comment removed for export] *)
| NMunmap (addr len : Z)                           (* [comment removed for export] *)
| NMprotect (addr len prot : Z).                   (* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs)
      | None => False
      end
  | _ => False
  end.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

(* [comment removed for export] *)
Definition minv (mo : Model) : Prop := m_vm_lazy mo = [].

Lemma minv_init : forall reserved brk0 mbase sp lim inp, minv (init_model reserved brk0 mbase sp lim inp).  (* [comment removed for export] *)
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (TASK_SIZE <? bv_unsigned addr + nZ) then true
    else
      let n := Z_to_bv 64 nZ in
      map_has (vm_maps h) addr n || munmap_free_ok h addr nZ.

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

(* [comment removed for export] *)
Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  mmap_off_aligned_b off && mmap_anon_b flags &&
  ((negb (w_is0 len) && (mmap_modeled_b prot flags off || mmap_noaccess_b prot flags off))
   || (if w_is0 len then mmap_plain_anon_b flags
       else if mmap_fixed_noaccess_b prot flags off then
         let nZ := page_round_up_Z (bv_unsigned len) in
         if (two_pow_64 <=? bv_unsigned addr + nZ) then true
         else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
         else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
         else if negb (0 <? bv_unsigned addr) then false
         else (region_free (vm_reserved h) addr (Z_to_bv 64 nZ) && map_contains (vm_maps h) addr (Z_to_bv 64 nZ))
              || region_free (vm_reserved h ++ vm_maps h) addr (Z_to_bv 64 nZ)
              || region_free (vm_reserved h) addr (Z_to_bv 64 nZ)
       else false)).

(* [comment removed for export] *)
Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_noreserve_b (Z_to_bv 64 flags) = false /\
      mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
  | NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
  | NMprotect addr len prot =>
      mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
  | _ => True
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_svc_inv : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep segs (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
                  X = SNext (mkCfg (nret ms eff) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\ evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  (* [comment removed for export] *)
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. eauto.
  - right; left. eexists _, _, _. repeat split; eauto.
  - right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; right. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_kit : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> P eff mo' evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, P eff mo' evs -> m_halted mo' = None /\ minv mo') ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
  /\ (forall eff mo' evs, P eff mo' evs -> sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, P eff mo' evs).
Proof.
  intros ms mo x8 P Hsvc Hh Hchar Hnu Hhalt. split; [|split].
  - intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
      as [(eff & mo' & mo'' & Hs & Hh' & Hm & ->) | [(eff & mo' & evs0 & Hs & Hh' & Hm & -> & ->) | [(eff & mo' & evs0 & code & Hs & Hh' & -> & ->) | [(eff & mo' & evs0 & sig & Hs & Hk & -> & ->) | (Hs & -> & ->)]]]].
    + exists eff, mo'. apply check_syscall_ok_iff in Hs. apply Hchar in Hs.
      rewrite (materialize_model_accesses_no_lazy mo' _ (proj2 (Hhalt _ _ _ Hs))) in Hm. inversion Hm; subst. auto.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs.
      rewrite (materialize_model_accesses_no_lazy mo' _ (proj2 (Hhalt _ _ _ Hs))) in Hm. discriminate.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs. apply Hhalt in Hs. destruct Hs; congruence.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs. apply Hhalt in Hs. destruct Hs as [Hh0 _].
      rewrite (m_killed_of_m_halted_none _ Hh0) in Hk. discriminate.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
  - intros eff mo' evs HP. unfold nret. eapply sstep_syscall; [exact Hh|exact Hsvc| |exact (proj1 (Hhalt _ _ _ HP))|].
    + apply check_syscall_ok_iff. apply Hchar. exact HP.
    + apply materialize_model_accesses_no_lazy. exact (proj2 (Hhalt _ _ _ HP)).
  - pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    + exists eff, mo', evs. apply Hchar. apply check_syscall_ok_iff. exact Hr.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.

End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PerNode.
Variable segs : list Segment.

Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> nstep n mo eff mo' evs) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) /\
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo').

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\
  (m_lim m' = m_lim m /\ m_time m' = m_time m /\ m_vm_lazy m' = m_vm_lazy m).  (* [comment removed for export] *)

#[using="Type"] Lemma vm_only_refl : forall m, vm_only m m.
Proof. intros; unfold vm_only; repeat split; reflexivity. Qed.

#[using="Type"] Lemma vm_only_halted : forall m m', vm_only m m' -> m_halted m' = m_halted m.
Proof. intros m m' (_ & _ & _ & H & _). unfold m_halted. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> minv mo -> minv mo'.
Proof. intros mo mo' (_ & _ & _ & _ & _ & _ & H) Hm. unfold minv in *. congruence. Qed.

#[using="Type"] Lemma vm_only_with_vmmaps : forall h m, vm_only m (with_vmmaps h m).
Proof. intros; unfold vm_only; repeat split; reflexivity. Qed.

#[using="Type"] Lemma maps_subtract_nil : forall lo hi, maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

#[using="Type"] Lemma vm_only_forget_range : forall lo hi m, minv m -> vm_only m (vm_forget_range lo hi m).
Proof.
  intros lo hi m Hm. unfold vm_forget_range, vm_only, minv in *. unfold m_vm_lazy in *.
  cbn. rewrite Hm. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. intros a b c (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). unfold vm_only. repeat split; congruence. Qed.

#[using="Type"] Lemma vm_only_forget_ranges : forall rs m, minv m -> vm_only m (forget_vm_ranges rs m).
Proof.
  induction rs as [|[a n] rs IH]; intros m Hm; cbn [forget_vm_ranges].
  - apply vm_only_refl.
  - eapply vm_only_trans; [apply vm_only_forget_range; exact Hm|]. apply IH.
    eapply minv_vm_only; [apply vm_only_forget_range; exact Hm| exact Hm].
Qed.

Ltac crush_check H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (? & ? & ?); subst
          | (match ?x with _ => _ end) = _ => destruct x eqn:?
          | (if ?x then _ else _) = _ => destruct x eqn:?
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).

#[using="Type"] Lemma check_brk_shape : forall req eff m m' evs,
  minv m -> check_brk req eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof.
  intros req eff m m' evs Hm H. unfold check_brk in H. crush_check H; split; try reflexivity; try apply vm_only_refl.
  unfold with_brk_next. eapply vm_only_trans; [apply vm_only_with_vmmaps|]. apply vm_only_forget_ranges.
  eapply minv_vm_only; [apply vm_only_with_vmmaps| exact Hm].
Qed.

#[using="Type"] Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.

Ltac vm_only_solve Hm :=
  repeat first [ apply vm_only_refl
               | apply vm_only_with_vmmaps
               | apply vm_only_forget_range; (exact Hm || (eapply minv_vm_only; [|exact Hm]))
               | progress (unfold with_mmap_destroyed, with_mmap_replacement, mprotect_model_next)
               | eapply vm_only_trans; [apply vm_only_with_vmmaps|] ].

#[using="Type"] Lemma check_mmap_shape : forall addr len prot flags fd off eff m m' evs,
  minv m -> mmap_noreserve_b flags = false ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof.
  intros until evs; intros Hm Hnr H. unfold check_mmap in H.
  crush_check H; split; try reflexivity; unfold with_mmap_replacement; rewrite ?with_mmap_backing_plain by exact Hnr; vm_only_solve Hm.
Qed.

#[using="Type"] Lemma check_munmap_shape : forall addr len eff m m' evs,
  minv m -> check_munmap addr len eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof.
  intros until evs; intros Hm H. unfold check_munmap in H. crush_check H; split; try reflexivity; vm_only_solve Hm.
Qed.

#[using="Type"] Lemma check_mprotect_shape : forall addr len prot eff m m' evs,
  minv m -> check_mprotect addr len prot eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof.
  intros until evs; intros Hm H. unfold check_mprotect in H. crush_check H; split; try reflexivity; vm_only_solve Hm.
Qed.

Ltac no_unm :=
  repeat first [ apply check_ret_only_no_unmodeled
               | discriminate
               | match goal with |- (match ?x with _ => _ end) <> _ => destruct x end
               | match goal with |- (if ?x then _ else _) <> _ => destruct x end
               | progress cbv zeta beta iota ].

#[using="Type"] Lemma munmap_safe_no_unmodeled : forall addr len eff m,
  munmap_safe_b addr len (m_vmmaps m) = true -> check_munmap addr len eff m <> CheckUnmodeled.
Proof.
  intros addr len eff m. unfold munmap_safe_b, check_munmap.
  destruct (negb _ || w_is0 len); [intros _; apply check_ret_only_no_unmodeled|]. cbv zeta.
  destruct (TASK_SIZE <? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (map_has _ _ _); [intros _; no_unm|]. cbn [orb]. intros ->. apply check_ret_only_no_unmodeled.
Qed.

#[using="Type"] Lemma mprotect_safe_no_unmodeled : forall addr len prot eff m,
  mprotect_safe_b addr len prot (m_vmmaps m) = true -> check_mprotect addr len prot eff m <> CheckUnmodeled.
Proof.
  intros addr len prot eff m. unfold mprotect_safe_b, check_mprotect.
  destruct (mprotect_grows_conflict_b prot); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (w_is0 len); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (mprotect_modeled_b prot); [|discriminate]. cbn [negb]. cbv zeta.
  destruct (map_contains (vm_noaccess _) _ _ && map_contains _ _ _); [intros _; no_unm|].
  cbn [orb]. intros ->. no_unm.
Qed.

#[using="Type"] Lemma mmap_safe_no_unmodeled : forall addr len prot flags fd off eff m,
  mmap_safe_b addr len prot flags fd off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros addr len prot flags fd off eff m. unfold mmap_safe_b, check_mmap.
  destruct (mmap_off_aligned_b off); [|discriminate].
  destruct (mmap_anon_b flags); [|discriminate]. cbn [negb andb].
  destruct (w_is0 len).
  { cbn [negb andb orb]. intros ->. apply check_ret_only_no_unmodeled. }
  cbn [negb andb].
  destruct (mmap_modeled_b prot flags off); [intros _; no_unm|].
  destruct (mmap_noaccess_b prot flags off); [intros _; no_unm|]. cbn [orb].
  destruct (mmap_fixed_noaccess_b prot flags off); [|discriminate]. cbv zeta.
  destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (_ <=? alloc_top _)); [discriminate|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (0 <? bv_unsigned addr)); [discriminate|].
  destruct (region_free (vm_reserved _) _ _ && map_contains _ _ _); [intros _; no_unm|]. cbn [orb].
  destruct (region_free (vm_reserved _ ++ _) _ _); [intros _; no_unm|]. cbn [orb].
  intros ->. no_unm.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mm_facts : forall ms mo n i x8 (chk : resp -> check_result),
  node_input n = Some i ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (evs = [] /\ syscall_spec i mo (Ok eff mo' evs))) ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_only mo mo' /\ evs = []) ->
  node_facts ms mo n.
Proof.
  intros ms mo n i x8 chk Hi Hn Hsvc Hminv Hh Hc1 Hc2 Hnu Hshape.
  exists x8. split; [exact Hsvc|]. split; [|split].
  - intros eff mo' evs. rewrite Hc1, Hn, <- check_syscall_ok_iff, Hc2. split; [|tauto].
    intros H. split; [|exact H]. exact (proj2 (Hshape _ _ _ H)).
  - intros eff. rewrite Hc1. apply Hnu.
  - intros eff mo' evs HP. apply Hn in HP as [_ HP]. apply check_syscall_ok_iff in HP. rewrite Hc2 in HP.
    apply Hshape in HP as [Hv _]. split.
    + rewrite (vm_only_halted _ _ Hv). exact Hh.
    + eapply minv_vm_only; eassumption.
Qed.

#[using="Type"] Lemma unsigned_sysno : forall k, 0 <= k < 2^64 -> bv_unsigned (Z_to_bv 64 k) = k.
Proof. intros k Hk. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hk. Qed.


#[using="Type"] Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof.
  intros z Hz. unfold w_is0. destruct (Z.eqb_spec z 0) as [->|Hne].
  - apply bv_eqb_refl.
  - destruct (bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0)) eqn:E; [|reflexivity].
    exfalso. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_sysno in E by lia. lia.
Qed.

#[using="Type"] Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_sysno by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma brk_facts : forall ms mo req,
  at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo -> node_facts ms mo (NBrk req).
Proof.
  intros ms mo req (Hsvc & Ha0) Hminv Hh _.
  eapply (mm_facts ms mo (NBrk req) _ _ (fun eff => check_brk (Z_to_bv 64 req) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. rewrite check_syscall_brk by (rewrite in_sysno_si; apply unsigned_sysno; lia). rewrite in_a0_si, Ha0. reflexivity.
  - intros eff. rewrite check_syscall_brk by (apply unsigned_sysno; lia). reflexivity.
  - intros [r ws zs us cs ci]. unfold check_brk. no_unm.
  - intros eff mo' evs. apply check_brk_shape. exact Hminv.
Qed.

#[using="Type"] Lemma mmap_facts : forall ms mo addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
  node_facts ms mo (NMmap addr len prot flags).
Proof.
  intros ms mo addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) Hminv Hh [Hnr Hsafe].
  eapply (mm_facts ms mo (NMmap addr len prot flags) _ _
            (fun eff => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                   (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. rewrite check_syscall_mmap by (rewrite in_sysno_si; apply unsigned_sysno; lia).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
  - intros eff. rewrite check_syscall_mmap by (apply unsigned_sysno; lia). reflexivity.
  - intros eff. apply mmap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mmap_shape; assumption.
Qed.

#[using="Type"] Lemma munmap_facts : forall ms mo addr len,
  at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
  node_facts ms mo (NMunmap addr len).
Proof.
  intros ms mo addr len (Hsvc & Ha0 & Ha1) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMunmap addr len) _ _
            (fun eff => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. rewrite check_syscall_munmap by (rewrite in_sysno_si; apply unsigned_sysno; lia).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1. reflexivity.
  - intros eff. rewrite check_syscall_munmap by (apply unsigned_sysno; lia). reflexivity.
  - intros eff. apply munmap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_munmap_shape. exact Hminv.
Qed.

#[using="Type"] Lemma mprotect_facts : forall ms mo addr len prot,
  at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
  node_facts ms mo (NMprotect addr len prot).
Proof.
  intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMprotect addr len prot) _ _
            (fun eff => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. rewrite check_syscall_mprotect by (rewrite in_sysno_si; apply unsigned_sysno; lia).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2. reflexivity.
  - intros eff. rewrite check_syscall_mprotect by (apply unsigned_sysno; lia). reflexivity.
  - intros eff. apply mprotect_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mprotect_shape. exact Hminv.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <-> (evs = [] /\ check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs).
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff.
  rewrite check_syscall_brk by (apply unsigned_sysno; lia). reflexivity.
Qed.

#[using="Type"] Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  (evs = [] /\ check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs).
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff.
  rewrite check_syscall_mmap by (apply unsigned_sysno; lia). reflexivity.
Qed.

#[using="Type"] Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  (evs = [] /\ check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs).
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff.
  rewrite check_syscall_munmap by (apply unsigned_sysno; lia). reflexivity.
Qed.

#[using="Type"] Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  (evs = [] /\ check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs).
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff.
  rewrite check_syscall_mprotect by (apply unsigned_sysno; lia). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  minv mo -> nsafe n mo ->
  nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [].
Proof.
  intros n mo eff mo' evs Hm Hs H. destruct n; try contradiction.
  - apply nstep_brk_iff in H as [_ H]. eapply check_brk_shape; eauto.
  - apply nstep_mmap_iff in H as [_ H]. destruct Hs as [Hnr _]. eapply check_mmap_shape; eauto.
  - apply nstep_munmap_iff in H as [_ H]. eapply check_munmap_shape; eauto.
  - apply nstep_mprotect_iff in H as [_ H]. eapply check_mprotect_shape; eauto.
Qed.

#[using="Type"] Lemma nstep_nil : forall n mo eff mo' evs, nstep n mo eff mo' evs -> evs = [].
Proof. intros n mo eff mo' evs H. destruct n; cbn [nstep] in H; tauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nsafe_mmap_rw : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
  intros addr len mo Hl. cbn [nsafe]. split; [reflexivity|]. unfold mmap_safe_b.
  unfold w_is0. destruct (bv_eqb (Z_to_bv 64 len) (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  exfalso. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_sysno in E by lia. lia.
Qed.

#[using="Type"] Lemma nsafe_mmap_none : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
  intros addr len mo Hl. cbn [nsafe]. split; [reflexivity|]. unfold mmap_safe_b.
  unfold w_is0. destruct (bv_eqb (Z_to_bv 64 len) (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  exfalso. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_sysno in E by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma minv_preserved : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> nsafe n mo -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hminv Hh Hs H.
  destruct (nstep_mm_vm_only n mo eff mo' evs Hminv Hs H) as [Hv _].
  split; [rewrite (vm_only_halted _ _ Hv); exact Hh | eapply minv_vm_only; eassumption].
Qed.

#[using="Type"] Lemma all_facts : forall n ms mo,
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
  (exists eff mo' evs, nstep n mo eff mo' evs) \/ match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end ->
  node_facts ms mo n.
Proof.
  intros n ms mo Hat Hminv Hh Hsafe Hmm.
  assert (Hn : match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end).
  { destruct Hmm as [(eff & mo' & evs & H)|H]; [destruct n; cbn [nstep] in H; tauto| exact H]. }
  destruct n; try contradiction.
  - apply brk_facts; assumption.
  - apply mmap_facts; assumption.
  - apply munmap_facts; assumption.
  - apply mprotect_facts; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mm_node_facts : forall n ms mo,
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros n ms mo Hne Hat Hminv Hh Hsafe.
  destruct (all_facts n ms mo Hat Hminv Hh Hsafe (or_intror Hne)) as (x8 & Hsvc & Hchar & Hnu & Hpres).
  destruct (node_kit segs ms mo x8 (nstep n mo) Hsvc Hh Hchar Hnu) as (Hc & Hs & Hp).
  { intros eff mo' evs HP. exact (Hpres _ _ _ HP). }
  split; [exact Hc|]. split; [|exact Hp].
  intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. auto.
Qed.

#[using="Type"] Lemma at_node_pending : forall n ms, at_node segs n ms -> ms_svc_pending ms <> None.
Proof.
  intros n ms Hat.
  assert (Hx : exists x8, ms_svc_pending ms = Some x8).
  { destruct n as [| | | | | | |c| | | |]; cbn [at_node] in Hat;
      first [ destruct Hat as [[H|H] _]; eexists; exact H
            | destruct Hat as [H _]; eexists; exact H
            | eexists; exact Hat ]. }
  destruct Hx as [x8 ->]. discriminate.
Qed.

End PerNode.
