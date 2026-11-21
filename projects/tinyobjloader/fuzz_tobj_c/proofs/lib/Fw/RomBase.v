(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): the read-only backing of a state, and system-call
   specifications that do not change when it grows.

   PORTED, STATEMENT AND PROOF, from
   the donor:
     projects/libreac/fuzz_ctrl/proofs/lib/Reusable/RomBase.v:17-254
   (the same text as projects/openssl/bignum/proofs/lib/VCommon/Cfg/RomBase.v).  The donor
   carries no tree vocabulary of its own: every name below [segs] is the model's, so the port
   is verbatim but for this tree's module path; its check in this tree is this unit's own
   build, not the donor's.

   WHY THIS TREE NEEDS IT.  At 75d69e00 [Run.run_scfg] reads a binary against
   [run_segments segs inp sp mb] = [segs ++ vdso_segments ..] from
   [init_config (run_segments ..) ..].  That configuration differs from [init_config segs ..]
   in ONE field, the read-only backing [ms_rom] (Run.v [init_machine_state]: [ms_rom] reads
   [memory_read mi_loaded_segments]); [segments_reserved] drops the pair, so the model part is
   the same.  No machine step reads [ms_rom]: only a system call reads it, through
   [Run.sys_input]'s [in_mem] := [ms_read_byte] (RiscvSemantics.v: [ms_mem] first, then
   [ms_rom]).  [sys_rob] is the one thing a configuration has to show for that growth to be
   invisible, and [Fw/RunSeg.v] is the transfer. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
(* Every other file in this cone carries these three -- Fw/{SysSpec,SysStep,Safety,RunSeg,
   SafetyAbort}.v and Fw3/SymCall.v, 6 of 6 checked.  This file was the only one without
   them, because it was ported verbatim from a donor whose tree does not use them.  An
   option set without [Local] is exported to importers, so the omission did not stay local
   to this file: it left the caches on for everything that Requires it. *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition wrom (ms : machine_state) (r : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := r |}.

Lemma wrom_eta : forall ms, wrom ms (ms_rom ms) = ms.
Proof. intros []; reflexivity. Qed.

Definition cwrom (c : config) (r : word -> option byte) : config :=
  mkCfg (wrom (cfg_ms c) r) (cfg_model c).

(** [r2] answers every byte [r1] answers, the same way. *)
Definition rom_ext (r1 r2 : word -> option byte) : Prop :=
  forall a b, r1 a = Some b -> r2 a = Some b.

Lemma rom_ext_refl : forall r, rom_ext r r.
Proof. intros r a b H. exact H. Qed.

Lemma rom_ext_trans : forall r1 r2 r3, rom_ext r1 r2 -> rom_ext r2 r3 -> rom_ext r1 r3.
Proof. intros r1 r2 r3 H1 H2 a b H. apply H2, H1, H. Qed.

(** The process's read view grows with the backing. *)
Lemma ms_read_byte_wrom_ext : forall ms r a b,
  rom_ext (ms_rom ms) r -> ms_read_byte ms a = Some b -> ms_read_byte (wrom ms r) a = Some b.
Proof.
  intros ms r a b Hr. unfold ms_read_byte. cbn [ms_mem ms_rom wrom].
  destruct (ms_mem ms a); [intro H; exact H | apply Hr].
Qed.

Lemma ms_read_bytes_aux_wrom : forall n ms r a bs,
  rom_ext (ms_rom ms) r -> ms_read_bytes_aux ms a n = Some bs ->
  ms_read_bytes_aux (wrom ms r) a n = Some bs.
Proof.
  induction n as [|n IH]; intros ms r a bs Hr H; [exact H|].
  cbn [ms_read_bytes_aux] in *.
  destruct (ms_read_byte ms a) as [b|] eqn:E; [|discriminate H].
  rewrite (ms_read_byte_wrom_ext ms r a b Hr E).
  destruct (ms_read_bytes_aux ms (a + 1) n) as [rest|] eqn:E2; [|discriminate H].
  rewrite (IH ms r (a + 1) rest Hr E2). exact H.
Qed.

Lemma ms_read_bytes_wrom : forall ms r a len bs,
  rom_ext (ms_rom ms) r -> ms_read_bytes ms a len = Some bs ->
  ms_read_bytes (wrom ms r) a len = Some bs.
Proof. intros ms r a len bs Hr. unfold ms_read_bytes. apply ms_read_bytes_aux_wrom. exact Hr. Qed.

(** ** System calls whose specification does not read [in_mem]

    [in_mem] is read only by the arms in the model's Sys/Fs/{EventPoll,Ioctl,Namei,Open,
    ReadWrite,Select,Stat}.v, Sys/Kernel/{Fork,Futex/Syscalls,Sched/Syscalls,Signal,Sys,
    Time/Hrtimer}.v and Sys/Net/Socket.v ([git grep in_mem]).  For every other arm the check is
    the same function of the input's other fields; each [memfree_NN] below is that fact for one
    number, by conversion. *)
Definition with_mem (i : SyscallInput) (mp : word -> option byte) : SyscallInput :=
  mkInput (in_sysno i) (in_args i) mp (in_wmem i).

Definition memfree (no : Z) : Prop :=
  forall i mp eff m, bv_unsigned (in_sysno i) = no ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.

Ltac memfree_tac := intros i mp eff m H; unfold check_syscall; cbn [with_mem in_sysno]; rewrite H; reflexivity.

(** close, read, exit, exit_group, set_tid_address, brk, munmap, mmap, mprotect, madvise
    (Sys/Fs/Open.v [close_spec]; Sys/Fs/ReadWrite.v [read_spec] reads only [in_wmem];
    Sys/Kernel/Exit; Sys/Mm/{Brk,Munmap,Mmap,Mprotect,Madvise}.v), and the credential
    getters. *)
Lemma memfree_57 : memfree 57. Proof. memfree_tac. Qed.
Lemma memfree_63 : memfree 63. Proof. memfree_tac. Qed.
Lemma memfree_93 : memfree 93. Proof. memfree_tac. Qed.
Lemma memfree_94 : memfree 94. Proof. memfree_tac. Qed.
Lemma memfree_96 : memfree 96. Proof. memfree_tac. Qed.
Lemma memfree_214 : memfree 214. Proof. memfree_tac. Qed.
Lemma memfree_215 : memfree 215. Proof. memfree_tac. Qed.
Lemma memfree_222 : memfree 222. Proof. memfree_tac. Qed.
Lemma memfree_226 : memfree 226. Proof. memfree_tac. Qed.
Lemma memfree_233 : memfree 233. Proof. memfree_tac. Qed.
Lemma memfree_172 : memfree 172. Proof. memfree_tac. Qed.
Lemma memfree_173 : memfree 173. Proof. memfree_tac. Qed.
Lemma memfree_174 : memfree 174. Proof. memfree_tac. Qed.
Lemma memfree_175 : memfree 175. Proof. memfree_tac. Qed.
Lemma memfree_176 : memfree 176. Proof. memfree_tac. Qed.
Lemma memfree_177 : memfree 177. Proof. memfree_tac. Qed.
Lemma memfree_178 : memfree 178. Proof. memfree_tac. Qed.

(** [memfree NN] for a known number. *)
Ltac memfree_lit :=
  first [ exact memfree_57 | exact memfree_63 | exact memfree_93 | exact memfree_94
        | exact memfree_96 | exact memfree_214 | exact memfree_215 | exact memfree_222
        | exact memfree_226 | exact memfree_233 | exact memfree_172 | exact memfree_173
        | exact memfree_174 | exact memfree_175 | exact memfree_176 | exact memfree_177
        | exact memfree_178 ].

(** ** Reads that succeed are the same over a larger memory view

    [State.read_cstr_aux] (openat's path, State.v) reads bytes [a, a+1, ...] until a NUL,
    each after [access_okb]; [State.cstr_access_len_aux] (the path's copy-in record) counts
    the same bytes.  When the read does not fault, every byte it reads is defined, so a view
    that answers those bytes the same way gives the same result. *)
Definition mem_ext (mp mp' : word -> option byte) : Prop :=
  forall a b, mp a = Some b -> mp' a = Some b.

Lemma mem_ext_read_byte_wrom : forall ms r,
  rom_ext (ms_rom ms) r -> mem_ext (ms_read_byte ms) (ms_read_byte (wrom ms r)).
Proof. intros ms r Hr a b. apply ms_read_byte_wrom_ext. exact Hr. Qed.

Lemma read_cstr_aux_ext : forall k mp mp' a,
  mem_ext mp mp' -> read_cstr_aux mp a k <> CstrFault ->
  read_cstr_aux mp' a k = read_cstr_aux mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a Hx Hnf; [reflexivity|].
  cbn [read_cstr_aux] in *.
  destruct (negb (access_okb a 1)); [exfalso; apply Hnf; reflexivity|].
  destruct (mp a) as [b|] eqn:E; [|exfalso; apply Hnf; reflexivity].
  rewrite (Hx a b E).
  destruct (bv_eqb b (Z_to_bv 8 0)); [reflexivity|].
  destruct (read_cstr_aux mp (a + 1) k) as [r| |] eqn:E2.
  - rewrite (IH mp mp' (a + 1) Hx ltac:(rewrite E2; discriminate)), E2. reflexivity.
  - rewrite (IH mp mp' (a + 1) Hx ltac:(rewrite E2; discriminate)), E2. reflexivity.
  - exfalso. apply Hnf. reflexivity.
Qed.

Lemma cstr_access_len_aux_ext : forall k mp mp' a,
  mem_ext mp mp' -> read_cstr_aux mp a k <> CstrFault ->
  cstr_access_len_aux mp' a k = cstr_access_len_aux mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a Hx Hnf; [reflexivity|].
  cbn [read_cstr_aux cstr_access_len_aux] in *.
  destruct (negb (access_okb a 1)); [reflexivity|].
  destruct (mp a) as [b|] eqn:E; [|exfalso; apply Hnf; reflexivity].
  rewrite (Hx a b E).
  destruct (bv_eqb b (Z_to_bv 8 0)); [reflexivity|].
  rewrite (IH mp mp' (a + 1) Hx); [reflexivity|].
  intro Hf. apply Hnf. rewrite Hf. reflexivity.
Qed.

Lemma read_cstr_ext : forall mp mp' a,
  mem_ext mp mp' -> read_cstr mp a <> CstrFault -> read_cstr mp' a = read_cstr mp a.
Proof. intros mp mp' a. apply read_cstr_aux_ext. Qed.

Lemma read_bytes_aux_ext : forall k mp mp' a bs,
  mem_ext mp mp' -> read_bytes_aux mp a k = Some bs -> read_bytes_aux mp' a k = Some bs.
Proof.
  induction k as [|k IH]; intros mp mp' a bs Hx H; [exact H|].
  cbn [read_bytes_aux] in *.
  destruct (mp a) as [b|] eqn:E; [|discriminate H].
  rewrite (Hx a b E).
  destruct (read_bytes_aux mp (a + 1) k) as [r|] eqn:E2; [|discriminate H].
  rewrite (IH mp mp' (a + 1) r Hx E2). exact H.
Qed.

Lemma read_bytes_map_ext : forall mp mp' a len bs,
  mem_ext mp mp' -> read_bytes_map mp a len = Some bs -> read_bytes_map mp' a len = Some bs.
Proof.
  intros mp mp' a len bs Hx. rewrite !read_bytes_map_eq. apply read_bytes_aux_ext. exact Hx.
Qed.

(** [State.read_u64] is a [read_bytes_map] of eight bytes and a decode (State.v:1116-1120),
    so it transports the same way: writev's iovec descriptors are read through it, and the
    [Hv1 .. Hv4] of SysSpec's [Writev1]/[Writev2] sections are exactly these. *)
Lemma read_u64_ext : forall mp mp' a v,
  mem_ext mp mp' -> read_u64 mp a = Some v -> read_u64 mp' a = Some v.
Proof.
  intros mp mp' a v Hx H. unfold read_u64 in *.
  destruct (read_bytes_map mp a (Z_to_bv 64 8)) as [bs|] eqn:E; [|discriminate H].
  rewrite (read_bytes_map_ext _ _ _ _ _ Hx E). exact H.
Qed.

Section Seg.
Variable segs : list Segment.

(** At a system-call configuration, the specification is the same for every larger backing.
    An instruction configuration has nothing to show. *)
Definition sys_rob (c : config) : Prop :=
  forall r x8, rom_ext (ms_rom (cfg_ms c)) r -> ms_svc_pending (cfg_ms c) = Some x8 ->
  forall o, syscall_spec (sys_input segs (wrom (cfg_ms c) r) x8) (cfg_model c) o
            <-> syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) o.

Lemma sys_rob_instr : forall c, ms_svc_pending (cfg_ms c) = None -> sys_rob c.
Proof. intros c H r x8 _ H'. congruence. Qed.

(** By the executable check: a check that is the same for the larger backing. *)
Lemma sys_rob_of_check : forall ms m,
  (forall r x8, rom_ext (ms_rom ms) r -> ms_svc_pending ms = Some x8 ->
     forall eff, check_syscall (sys_input segs (wrom ms r) x8) eff m
                 = check_syscall (sys_input segs ms x8) eff m) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m H r x8 Hr Hs o. cbn [cfg_ms cfg_model] in *.
  destruct o as [eff m' evs|].
  - rewrite <- !check_syscall_ok_iff. rewrite (H r x8 Hr Hs eff). reflexivity.
  - set (e0 := mkEffect (Z_to_bv 64 0) [] []).
    rewrite <- (check_syscall_err_iff (sys_input segs (wrom ms r) x8) e0 m).
    rewrite <- (check_syscall_err_iff (sys_input segs ms x8) e0 m).
    rewrite (H r x8 Hr Hs e0). reflexivity.
Qed.

(** By a characterisation of the outcomes that holds at every larger backing (the original
    backing included). *)
Lemma sys_rob_of_char : forall ms m x8 (Q : outcome SyscallEffect -> Prop),
  ms_svc_pending ms = Some x8 ->
  (forall r, rom_ext (ms_rom ms) r ->
     forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> Q o) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Q Hs HQ r x8' Hr Hs' o. cbn [cfg_ms cfg_model] in *.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (HQ r Hr o).
  pose proof (HQ (ms_rom ms) (rom_ext_refl _) o) as H0. rewrite wrom_eta in H0.
  symmetry. exact H0.
Qed.

Lemma sys_input_wrom : forall ms r x8,
  sys_input segs (wrom ms r) x8 = with_mem (sys_input segs ms x8) (ms_read_byte (wrom ms r)).
Proof. reflexivity. Qed.

(** A system call whose specification does not read [in_mem]. *)
Lemma sys_rob_memfree : forall ms m x8,
  ms_svc_pending ms = Some x8 -> memfree (bv_unsigned x8) -> sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs Hmf. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite sys_input_wrom. apply Hmf. reflexivity.
Qed.

(** A system call whose check DOES read [in_mem], but only through reads that SUCCEED.

    THIS IS THE LEMMA THE FOUR MEMORY-READING NUMBERS NEED, AND WIDENING [memfree_lit] IS NOT
    AN ALTERNATIVE TO IT: [memfree no] (:88-90) quantifies over an ARBITRARY replacement
    memory [mp], and that statement is FALSE for 29, 56, 64 and 66 --
      29  [check_ioctl]'s FdDgram + SIOCGIFINDEX arm is [check_siocgifindex (in_arg i 2) i],
          which does [copy_bytes_map (in_mem i) argp IFREQ_SIZE]
          (75d69e00:theories/LinuxProcessSem/Checks/Sys/Fs/Ioctl.v:118, 192-195)
      56  [openat_check]'s right-hand side is [check_openat_body i dirfd pathp ..], and the
          path is read out of memory
      64, 66  write and writev read the user buffer and the iovecs.
    [memfree_tac] would not fail for a tactic reason at those numbers; the goal is false, and
    a [memfree_64] would be a false lemma.

    [sys_rob] does not ask for that.  [rom_ext] only GROWS the backing, so a read that
    SUCCEEDED under the smaller view returns the same bytes under the larger one -- which is
    exactly what the block at :126-188 above establishes, and what it was written for.  This
    lemma is the bridge: it hands the caller an arbitrary EXTENSION of the run's own memory
    rather than an arbitrary memory, so the caller may use the run's own read hypotheses,
    transported by [read_bytes_map_ext] (:184) or [read_cstr_ext] (:169). *)
Lemma sys_rob_of_mem_ext : forall ms m x8,
  ms_svc_pending ms = Some x8 ->
  (forall mp, mem_ext (ms_read_byte ms) mp ->
     forall eff, check_syscall (with_mem (sys_input segs ms x8) mp) eff m
               = check_syscall (sys_input segs ms x8) eff m) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs H. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite sys_input_wrom. apply H. apply mem_ext_read_byte_wrom. exact Hr.
Qed.

(** exit (93) and exit_group (94). *)
Lemma sys_rob_exit : forall ms m x8,
  ms_svc_pending ms = Some x8 -> (bv_unsigned x8 = 93 \/ bv_unsigned x8 = 94)%Z ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs [E|E]; apply (sys_rob_memfree ms m x8 Hs); rewrite E;
    first [exact memfree_93 | exact memfree_94].
Qed.
End Seg.

(** [memfree] at a number a hypothesis names.

    THIS IS THE DONOR TEXT.  The extra arms a variant of this tactic carries -- a
    [vm_compute]/[change] arm, the goal-only arms first, [memfree_of_eq] and three
    conversion-free arms -- do not repair the failure reported at Fw3/SymHeap.v:288,
    because [rob_auto] is not what fails there.  The column span in that file's own
    error settles it: on line 288, 0-based, [rob_auto] spans
    42-50 and the trailing [eassumption] spans 96-107, and Rocq blames 96-107.  [rob_auto]
    discharges the [sys_rob] premise correctly at every one of the eight sites; the
    failure is fifty columns to its right, in the [munmap_exact_only_ok] discharge, and
    the goal [eassumption] cannot close there is an exact-unmap
    rewrite identity, [maps_subtract ... = map_remove ...], which is in no hypothesis.

    So the extra arms fix nothing that is broken, and a patch kept for a
    withdrawn reason is worse than no patch: the next reader inherits the reason with it.
    This text is the libreac/openssl donor's, byte for byte,
    and it builds (measured). *)
Ltac memfree_auto :=
  repeat match goal with
         | H : bv_unsigned ?x = _ |- memfree (bv_unsigned ?x) => rewrite H
         | H : ?x = Z_to_bv 64 _ |- memfree (bv_unsigned ?x) =>
             rewrite H; rewrite Z_to_bv_unsigned; rewrite bv_wrap_small by (unfold bv_modulus; lia)
         end;
  memfree_lit.

(** [sys_rob] at an instruction configuration, or at a system call whose number a hypothesis
    names and whose specification does not read [in_mem]. *)
Ltac rob_auto :=
  first
    [ apply sys_rob_instr; cbn [cfg_ms]; first [assumption | reflexivity]
    | eapply sys_rob_memfree; [first [eassumption | reflexivity] |]; memfree_auto ].
