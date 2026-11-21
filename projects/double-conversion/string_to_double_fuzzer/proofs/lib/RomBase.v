(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 08b1429; copied unchanged from openssl/hashtable Common/Cfg/RomBase.v):
   the read-only backing of a state, and system-call
   specifications that do not change when it grows.  [ShapeAlg.rz_node] and [SpinAlg.srz_node]
   ask [sys_rob] at each node, so that a walk over a binary's own segments lifts to the run's
   segment list ([RomStable.realizes_wrom], [RomStable.run_init]).

   Only a system call reads [ms_rom]: [Run.sys_input]'s [in_mem] is [ms_read_byte]
   (RiscvSemantics.v: [ms_mem] first, then [ms_rom]); no machine step reads it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
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


(** ** System calls whose specification does not read [in_mem]

    [in_mem] is read only by the arms in the model's Sys/Fs/{EventPoll,Ioctl,Namei,Open,
    ReadWrite,Select,Stat}.v, Sys/Kernel/{Fork,Futex/Syscalls,Sched/Syscalls,Signal,Sys,
    Time/Hrtimer}.v and Sys/Net/Socket.v (LPS 08b1429, [git grep in_mem]).  For every other
    arm the check is the same function of the input's other fields; each [memfree_NN] below is
    that fact for one number, by conversion. *)
Definition with_mem (i : SyscallInput) (mp : word -> option byte) : SyscallInput :=
  mkInput (in_sysno i) (in_args i) mp (in_wmem i).

Definition memfree (no : Z) : Prop :=
  forall i mp eff m, bv_unsigned (in_sysno i) = no ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.

Ltac memfree_tac := intros i mp eff m H; unfold check_syscall; cbn [with_mem in_sysno]; rewrite H; reflexivity.

(** close, read, exit, exit_group, set_tid_address, brk, munmap, mmap, mprotect (Sys/Fs/Open.v
    [close_spec]; Sys/Fs/ReadWrite.v [read_spec] reads only [in_wmem]; Sys/Kernel/Exit;
    Sys/Mm/{Brk,Munmap,Mmap,Mprotect}.v), and the credential getters. *)
Lemma memfree_57 : memfree 57. Proof. memfree_tac. Qed.
Lemma memfree_63 : memfree 63. Proof. memfree_tac. Qed.
Lemma memfree_93 : memfree 93. Proof. memfree_tac. Qed.
Lemma memfree_94 : memfree 94. Proof. memfree_tac. Qed.
Lemma memfree_96 : memfree 96. Proof. memfree_tac. Qed.
Lemma memfree_214 : memfree 214. Proof. memfree_tac. Qed.
Lemma memfree_215 : memfree 215. Proof. memfree_tac. Qed.
Lemma memfree_222 : memfree 222. Proof. memfree_tac. Qed.
Lemma memfree_226 : memfree 226. Proof. memfree_tac. Qed.
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
        | exact memfree_226 | exact memfree_172 | exact memfree_173 | exact memfree_174
        | exact memfree_175 | exact memfree_176 | exact memfree_177 | exact memfree_178 ].


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

(** By a closed form: both checks equal the same function of the arguments. *)
Lemma sys_rob_of_closed : forall ms m (F : SyscallEffect -> check_result),
  (forall ms', rom_ext (ms_rom ms) (ms_rom ms') ->
     ms_regs ms' = ms_regs ms -> ms_mem ms' = ms_mem ms -> ms_svc_pending ms' = ms_svc_pending ms ->
     forall x8, ms_svc_pending ms' = Some x8 ->
     forall eff, check_syscall (sys_input segs ms' x8) eff m = F eff) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m F H. apply sys_rob_of_check. intros r x8 Hr Hs eff.
  rewrite (H (wrom ms r) Hr eq_refl eq_refl eq_refl x8 Hs eff).
  rewrite (H ms (rom_ext_refl _) eq_refl eq_refl eq_refl x8 Hs eff).
  reflexivity.
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
End Seg.

(** [sys_rob] at an instruction configuration, or at a system call whose number a hypothesis
    names and whose specification does not read [in_mem]. *)
Ltac rob_auto :=
  first
    [ apply sys_rob_instr; cbn [cfg_ms]; first [assumption | reflexivity]
    | eapply sys_rob_memfree; [first [eassumption | reflexivity] |];
      repeat match goal with
             | H : bv_unsigned ?x = _ |- memfree (bv_unsigned ?x) => rewrite H
             | H : ?x = Z_to_bv 64 _ |- memfree (bv_unsigned ?x) =>
                 rewrite H; rewrite Z_to_bv_unsigned; rewrite bv_wrap_small by (unfold bv_modulus; lia)
             end;
      memfree_lit ].
