(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Export Mmap Mprotect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* The memory-management syscalls brk (214), munmap (215), mmap (222) and mprotect (226), read three ways.
   1. At a fixed syscall number, syscall_spec unfolds to that call's own spec on the call's register arguments. *)

Lemma syscall_spec_brk inp st res :
  bv_unsigned (in_sysno inp) = 214 ->
  syscall_spec inp st res <-> brk_spec (in_arg inp 0) inp st res.
Proof. intro Hno. unfold syscall_spec, dispatch. rewrite Hno. apply iff_refl. Qed.

Lemma syscall_spec_munmap inp st res :
  bv_unsigned (in_sysno inp) = 215 ->
  syscall_spec inp st res <-> munmap_spec (in_arg inp 0) (in_arg inp 1) inp st res.
Proof. intro Hno. unfold syscall_spec, dispatch. rewrite Hno. apply iff_refl. Qed.

Lemma syscall_spec_mmap inp st res :
  bv_unsigned (in_sysno inp) = 222 ->
  syscall_spec inp st res <->
  mmap_spec (in_arg inp 0) (in_arg inp 1) (in_arg inp 2) (in_arg inp 3) (in_arg inp 4) (in_arg inp 5)
    inp st res.
Proof. intro Hno. unfold syscall_spec, dispatch. rewrite Hno. apply iff_refl. Qed.

Lemma syscall_spec_mprotect inp st res :
  bv_unsigned (in_sysno inp) = 226 ->
  syscall_spec inp st res <-> mprotect_spec (in_arg inp 0) (in_arg inp 1) (in_arg inp 2) inp st res.
Proof. intro Hno. unfold syscall_spec, dispatch. rewrite Hno. apply iff_refl. Qed.

(* 2. A successful outcome of the spec is exactly a CheckOk of the call's executable check, with the same final state
      and events. *)

Lemma spec_brk_iff inp st eff st' evs :
  bv_unsigned (in_sysno inp) = 214 ->
  syscall_spec inp st (Ok eff st' evs) <-> check_brk (in_arg inp 0) eff st = CheckOk st' evs.
Proof.
  intro Hno. rewrite (syscall_spec_brk inp st (Ok eff st' evs) Hno).
  split; intro Hc; [eapply check_brk_complete_ok | eapply check_brk_sound_ok]; eassumption.
Qed.

Lemma spec_munmap_iff inp st eff st' evs :
  bv_unsigned (in_sysno inp) = 215 ->
  syscall_spec inp st (Ok eff st' evs) <->
  check_munmap (in_arg inp 0) (in_arg inp 1) eff st = CheckOk st' evs.
Proof.
  intro Hno. rewrite (syscall_spec_munmap inp st (Ok eff st' evs) Hno).
  split; intro Hc; [eapply check_munmap_complete_ok | eapply check_munmap_sound_ok]; eassumption.
Qed.

Lemma spec_mmap_iff inp st eff st' evs :
  bv_unsigned (in_sysno inp) = 222 ->
  syscall_spec inp st (Ok eff st' evs) <->
  check_mmap (in_arg inp 0) (in_arg inp 1) (in_arg inp 2) (in_arg inp 3) (in_arg inp 4) (in_arg inp 5) eff st
    = CheckOk st' evs.
Proof.
  intro Hno. rewrite (syscall_spec_mmap inp st (Ok eff st' evs) Hno).
  split; intro Hc; [eapply check_mmap_complete_ok | eapply check_mmap_sound_ok]; eassumption.
Qed.

Lemma spec_mprotect_iff inp st eff st' evs :
  bv_unsigned (in_sysno inp) = 226 ->
  syscall_spec inp st (Ok eff st' evs) <->
  check_mprotect (in_arg inp 0) (in_arg inp 1) (in_arg inp 2) eff st = CheckOk st' evs.
Proof.
  intro Hno. rewrite (syscall_spec_mprotect inp st (Ok eff st' evs) Hno).
  split; intro Hc; [eapply check_mprotect_complete_ok | eapply check_mprotect_sound_ok]; eassumption.
Qed.

(* 3. When the spec says the outcome is not modelled, the executable check says so too, for any effect. *)

Lemma spec_brk_unmodeled inp st eff :
  bv_unsigned (in_sysno inp) = 214 ->
  syscall_spec inp st Unmodeled -> check_brk (in_arg inp 0) eff st = CheckUnmodeled.
Proof.
  intros Hno Hs. rewrite (syscall_spec_brk inp st Unmodeled Hno) in Hs.
  eapply check_brk_complete_unmodeled. eassumption.
Qed.

Lemma spec_munmap_unmodeled inp st eff :
  bv_unsigned (in_sysno inp) = 215 ->
  syscall_spec inp st Unmodeled -> check_munmap (in_arg inp 0) (in_arg inp 1) eff st = CheckUnmodeled.
Proof.
  intros Hno Hs. rewrite (syscall_spec_munmap inp st Unmodeled Hno) in Hs.
  eapply check_munmap_complete_unmodeled. eassumption.
Qed.

Lemma spec_mmap_unmodeled inp st eff :
  bv_unsigned (in_sysno inp) = 222 ->
  syscall_spec inp st Unmodeled ->
  check_mmap (in_arg inp 0) (in_arg inp 1) (in_arg inp 2) (in_arg inp 3) (in_arg inp 4) (in_arg inp 5) eff st
    = CheckUnmodeled.
Proof.
  intros Hno Hs. rewrite (syscall_spec_mmap inp st Unmodeled Hno) in Hs.
  eapply check_mmap_complete_unmodeled. eassumption.
Qed.

Lemma spec_mprotect_unmodeled inp st eff :
  bv_unsigned (in_sysno inp) = 226 ->
  syscall_spec inp st Unmodeled ->
  check_mprotect (in_arg inp 0) (in_arg inp 1) (in_arg inp 2) eff st = CheckUnmodeled.
Proof.
  intros Hno Hs. rewrite (syscall_spec_mprotect inp st Unmodeled Hno) in Hs.
  eapply check_mprotect_complete_unmodeled. eassumption.
Qed.
