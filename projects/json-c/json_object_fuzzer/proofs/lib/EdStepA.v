From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdBridge.
Import ListNotations.

Lemma ns_sysno : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff Hn. apply spurious_refusal_family_on. unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|reflexivity].
  destruct (ia_family a) eqn:F; try reflexivity.
  exfalso. exact (Hn (alloc_family_dispatched _ _ E F)).
Qed.

Lemma ns_sysno_eq : forall i m eff no,
  bv_unsigned (in_sysno i) = no -> existsb (Z.eqb no) alloc_mark_sysnos = false ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff no Hno Hb. apply ns_sysno. rewrite Hno. intros Hin.
  assert (Ht : existsb (Z.eqb no) alloc_mark_sysnos = true)
    by (apply existsb_exists; exists no; split; [exact Hin | apply Z.eqb_refl]).
  rewrite Ht in Hb. discriminate Hb.
Qed.

Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = errno_ret_in mmap_errnos r.
Proof. intros i m r H. unfold refusal_b. cbv zeta. rewrite H. reflexivity. Qed.

Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = errno_ret_in mprotect_errnos r.
Proof. intros i m r H. unfold refusal_b. cbv zeta. rewrite H. reflexivity. Qed.

Lemma family_off_222 : forall i, bv_unsigned (in_sysno i) = 222%Z ->
  injected_family_off (alloc_only_cfg false) i = true.
Proof. intros i H. unfold injected_family_off. rewrite H. reflexivity. Qed.

Lemma family_off_226 : forall i, bv_unsigned (in_sysno i) = 226%Z ->
  injected_family_off (alloc_only_cfg false) i = true.
Proof. intros i H. unfold injected_family_off. rewrite H. reflexivity. Qed.

Lemma ns_mmap_ret : forall i m eff, bv_unsigned (in_sysno i) = 222%Z ->
  errno_ret_in mmap_errnos (eff_ret eff) = false ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff H Hr. apply spurious_refusal_not_refusal.
  rewrite (refusal_b_222 i m _ H). exact Hr.
Qed.

Lemma ns_mprotect_ret : forall i m eff, bv_unsigned (in_sysno i) = 226%Z ->
  errno_ret_in mprotect_errnos (eff_ret eff) = false ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff H Hr. apply spurious_refusal_not_refusal.
  rewrite (refusal_b_226 i m _ H). exact Hr.
Qed.

Lemma sp_mmap_of_ok : forall i m eff eff' m' evs', bv_unsigned (in_sysno i) = 222%Z ->
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  check_syscall i eff' m = CheckOk m' evs' ->
  errno_ret_in mmap_errnos (eff_ret eff') = false ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff eff' m' evs' H Hr Hc Hr'. split; [exact (family_off_222 i H)|]. split.
  - rewrite (refusal_b_222 i m _ H). exact Hr.
  - exists eff', m', evs'. split; [apply check_syscall_ok_iff; exact Hc|].
    rewrite (refusal_b_222 i m _ H). exact Hr'.
Qed.

Lemma sp_mprotect_of_ok : forall i m eff eff' m' evs', bv_unsigned (in_sysno i) = 226%Z ->
  errno_ret_in mprotect_errnos (eff_ret eff) = true ->
  check_syscall i eff' m = CheckOk m' evs' ->
  errno_ret_in mprotect_errnos (eff_ret eff') = false ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff eff' m' evs' H Hr Hc Hr'. split; [exact (family_off_226 i H)|]. split.
  - rewrite (refusal_b_226 i m _ H). exact Hr.
  - exists eff', m', evs'. split; [apply check_syscall_ok_iff; exact Hc|].
    rewrite (refusal_b_226 i m _ H). exact Hr'.
Qed.

Lemma mmap_errnos_below_top : forall (a : word) (h : VmMaps) (nZ : Z), (0 <= nZ)%Z ->
  (bv_unsigned a + nZ <= alloc_top h)%Z -> errno_ret_in mmap_errnos a = false.
Proof.
  intros a h nZ Hn Hle. unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r.
  apply ed_bv_eqb_false. exact (ed_below_top_ne_enomem a h nZ Hn Hle).
Qed.

Lemma mprotect_errnos_zero : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

Lemma ns_same_ret : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> eff_ret eff' = eff_ret eff) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff H (_ & Hr & eff' & m' & evs' & Hs & Hr').
  rewrite (H _ _ _ Hs), Hr in Hr'. discriminate Hr'.
Qed.

Lemma brk_grow_grant_ns : forall i req m eff,
  bv_unsigned (in_sysno i) = 214%Z -> in_arg i 0 = req -> w_is0 req = false ->
  (bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req)%Z ->
  eff_ret eff = req ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i req m eff H1 H2 Hw Hmin Hlt Hr. apply spurious_refusal_not_refusal.
  rewrite (ed_brk_grow_refusal i req m _ (conj H1 H2) (conj Hw (conj Hmin Hlt))), Hr.
  apply ed_bv_eqb_false. intros E. rewrite E in Hlt. lia.
Qed.

Lemma brk_grow_keep_sp : forall i req m eff,
  bv_unsigned (in_sysno i) = 214%Z -> in_arg i 0 = req -> w_is0 req = false ->
  (bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req)%Z ->
  eff_ret eff = vm_brk (m_vmmaps m) -> brk_grow_ok m req req = true ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i req m eff H1 H2 Hw Hmin Hlt Hr Hok.
  exact (proj2 (ed_brk_grow_keep_spurious_iff i req m eff (conj H1 H2) (conj Hw (conj Hmin Hlt)) Hr) Hok).
Qed.
