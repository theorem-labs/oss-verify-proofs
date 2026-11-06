(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Export X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Common Require Export AllocRefusal.
Import ListNotations.
Open Scope bv_scope.

Lemma bv_eqb_refl : forall {n : N} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

Lemma word_unsigned_range : forall (w : word),
(0 <= bv_unsigned w < two_pow_64)%Z.
Proof.
intros w. pose proof (bv_unsigned_in_range _ w) as H.
unfold two_pow_64. unfold bv_modulus in H.
change (Z.of_N 64) with 64%Z in H. exact H.
Qed.

Lemma errno_ret_unsigned : forall e,
(1 <= e)%Z -> (e <= 4095)%Z ->
bv_unsigned (errno_ret e) = (two_pow_64 - e)%Z.
Proof.
intros e H1 H2. unfold errno_ret, two_pow_64.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (Z.of_N 64) with 64%Z.
replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma errno_ret_error_b : forall e,
(1 <= e)%Z -> (e <= 4095)%Z -> addr_is_error_b (errno_ret e) = true.
Proof.
intros e H1 H2. unfold addr_is_error_b.
rewrite (errno_ret_unsigned e H1 H2). unfold two_pow_64.
apply Z.ltb_lt. lia.
Qed.

Definition errnos_ok (es : list Z) : bool :=
forallb (fun e => (1 <=? e)%Z && (e <=? 4095)%Z) es.

Lemma errnos_ok_range : forall es e,
errnos_ok es = true -> In e es -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof.
induction es as [|x es IH]; intros e Hok HIn; [destruct HIn|].
cbn in Hok. apply andb_true_iff in Hok as [Hx Hok].
apply andb_true_iff in Hx as [H1 H2].
destruct HIn as [-> | HIn];
[ split; apply Z.leb_le; assumption
| apply IH; assumption ].
Qed.

Lemma read_bytes_aux_prefix : forall k n mp a w,
(k <= n)%nat -> read_bytes_aux mp a n = Some w ->
read_bytes_aux mp a k = Some (firstn k w).
Proof.
induction k as [|k IH]; intros n mp a w Hk Hw; [reflexivity|].
destruct n as [|n]; [lia|].
cbn in Hw. destruct (mp a) as [b|] eqn:Hb; [|discriminate].
destruct (read_bytes_aux mp (a + 1) n) as [r|] eqn:Hr; [|discriminate].
inversion Hw; subst w.
cbn. rewrite Hb. rewrite (IH n mp (a + 1) r ltac:(lia) Hr). reflexivity.
Qed.

Lemma read_bytes_map_prefix : forall mp a len k w,
(bv_unsigned k <= bv_unsigned len)%Z -> read_bytes_map mp a len = Some w ->
read_bytes_map mp a k = Some (firstn (word_to_nat k) w).
Proof.
intros mp a len k w Hk Hw. rewrite read_bytes_map_eq in *.
unfold word_to_nat in *.
apply read_bytes_aux_prefix with (n := Z.to_nat (bv_unsigned len));
[lia | assumption].
Qed.

Lemma read_bytes_aux_length : forall mp k a w,
read_bytes_aux mp a k = Some w -> length w = k.
Proof.
intros mp k; induction k as [|k IH]; intros a w Hw; cbn in Hw.
- inversion Hw. reflexivity.
- destruct (mp a); [|discriminate].
destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
inversion Hw; subst. cbn. now rewrite (IH _ _ Hr).
Qed.

Lemma read_bytes_map_length : forall mp a len w,
read_bytes_map mp a len = Some w -> Z.of_nat (length w) = bv_unsigned len.
Proof.
intros mp a len w Hw. rewrite read_bytes_map_eq in Hw.
unfold word_to_nat in Hw.
rewrite (read_bytes_aux_length _ _ _ _ Hw).
pose proof (word_unsigned_range len). lia.
Qed.

Lemma readable_bytes_aux_full : forall mp k a w,
read_bytes_aux mp a k = Some w -> readable_bytes_aux mp a k = w.
Proof.
intros mp k; induction k as [|k IH]; intros a w Hw; cbn in *.
- now inversion Hw.
- destruct (mp a); [|discriminate].
destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
inversion Hw; subst. now rewrite (IH _ _ Hr).
Qed.

Lemma readable_bytes_full : forall mp a len w,
read_bytes_map mp a len = Some w -> readable_bytes mp a len = w.
Proof.
intros. rewrite read_bytes_map_eq in *. rewrite readable_bytes_eq.
now apply readable_bytes_aux_full.
Qed.

Lemma len_word_unsigned : forall {A} (l : list A),
(Z.of_nat (length l) < two_pow_64)%Z ->
bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
intros A l Hl. unfold len_word.
rewrite Z_to_bv_small; [reflexivity|].
unfold bv_modulus. change (Z.of_N 64) with 64%Z.
unfold two_pow_64 in Hl. lia.
Qed.

Lemma firstn_length_le_Z : forall {A} (l : list A) r,
(0 <= r)%Z -> (r <= Z.of_nat (length l))%Z ->
Z.of_nat (length (firstn (Z.to_nat r) l)) = r.
Proof.
intros A l r H0 Hle. rewrite firstn_length_le; lia.
Qed.

Lemma len_word_firstn_ret : forall (ret : word) {A} (l : list A),
(0 <= bv_unsigned ret <= Z.of_nat (length l))%Z ->
len_word (firstn (Z.to_nat (bv_unsigned ret)) l) = ret.
Proof.
intros ret A l H. unfold len_word.
rewrite (firstn_length_le_Z l (bv_unsigned ret)) by lia.
apply Z_to_bv_bv_unsigned.
Qed.

Lemma gather_prefix_full : forall mp iovs bs,
gather_iovecs mp iovs = Some bs -> gather_prefix mp iovs = bs.
Proof.
induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
- now inversion Hg.
- destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
inversion Hg; subst.
rewrite (readable_bytes_full _ _ _ _ Hw).
rewrite (read_bytes_map_length _ _ _ _ Hw), Z.eqb_refl.
now rewrite (IH _ eq_refl).
Qed.

Lemma gather_iovecs_length : forall mp iovs bs,
gather_iovecs mp iovs = Some bs -> Z.of_nat (length bs) = iovs_total iovs.
Proof.
induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
- now inversion Hg.
- destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
inversion Hg; subst.
rewrite length_app, Nat2Z.inj_add.
rewrite (read_bytes_map_length _ _ _ _ Hw), (IH _ eq_refl). reflexivity.
Qed.

Lemma page_round_up_Z_nonneg : forall z,
(0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof.
intros z Hz. unfold page_round_up_Z, page_size.
apply Z.mul_nonneg_nonneg; [|lia].
apply Z.div_pos; lia.
Qed.

Lemma page_round_up_Z_mono : forall a b,
(a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
intros a b H. unfold page_round_up_Z, page_size.
apply Z.mul_le_mono_nonneg_r; [lia|].
apply Z.div_le_mono; lia.
Qed.

Definition access_ok_walk_max : Z := 16777216%Z.

Lemma access_ok_walk_max_lt_clamp : (access_ok_walk_max < MAX_RW_COUNT)%Z.
Proof. reflexivity. Qed.

Lemma alloc_top_of_init_sp : forall h h',
vm_init_sp h' = vm_init_sp h -> alloc_top h' = alloc_top h.
Proof. intros h h' E. unfold alloc_top. rewrite E. reflexivity. Qed.

Lemma alloc_top_window : forall h,
(sp_window_lo <= bv_unsigned (vm_init_sp h) <= sp_window_hi)%Z ->
(alloc_ceiling_lo <= alloc_top h <= alloc_ceiling_hi)%Z.
Proof.
intros h H. unfold sp_window_lo, sp_window_hi in H.
unfold alloc_top, stack_max_size, alloc_ceiling_lo, alloc_ceiling_hi. lia.
Qed.

Lemma alloc_top_le_max : forall h,
(bv_unsigned (vm_init_sp h) <= sp_window_hi)%Z -> (alloc_top h <= 0x7fffff800000)%Z.
Proof. intros h H. unfold sp_window_hi in H. unfold alloc_top, stack_max_size. lia. Qed.

Ltac sys_unfold :=
unfold record_copyins, with_copyins,
err_ret, ret_only, errno_from, lowest_fd,
set_fds, set_vmmaps, forget_vm_range,
set_stdin, set_fs, set_halted, set_tid,
get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
bind, pure, choose, alt, unmodeled, emit in *.

Lemma Ok_inj {A} : forall (x x' : A) m m' e e',
Ok x m e = Ok x' m' e' -> x = x' /\ m = m' /\ e = e'.
Proof. intros x x' m m' e e' H. injection H. auto. Qed.

Lemma Ok_Unmodeled {A} : forall (x : A) m e, Ok x m e = Unmodeled -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Unmodeled_Ok {A} : forall (x : A) m e, Unmodeled = Ok x m e -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Some_inj' {A} : forall (x y : A), Some x = Some y -> x = y.
Proof. intros x y H. injection H. auto. Qed.

Lemma Some_None {A} : forall (x : A), Some x = None -> False.
Proof. intros x H. discriminate H. Qed.

Lemma None_Some {A} : forall (x : A), None = Some x -> False.
Proof. intros x H. discriminate H. Qed.

Ltac inv_sys :=
repeat first
[ progress subst
| match goal with
| H : exists _, _ |- _ => destruct H
| H : _ /\ _ |- _ => destruct H
| H : Ok _ _ _ = Ok _ _ _ |- _ => apply Ok_inj in H; destruct H as (? & ? & ?); subst
| H : Ok _ _ _ = Unmodeled |- _ => exfalso; exact (Ok_Unmodeled _ _ _ H)
| H : Unmodeled = Ok _ _ _ |- _ => exfalso; exact (Unmodeled_Ok _ _ _ H)
| H : Some _ = Some _ |- _ => apply Some_inj' in H; subst
| H : Some _ = None |- _ => exfalso; exact (Some_None _ H)
| H : None = Some _ |- _ => exfalso; exact (None_Some _ H)
| H : False |- _ => contradiction
| H : true = false |- _ => exfalso; exact (Bool.diff_true_false H)
| H : false = true |- _ => exfalso; exact (Bool.diff_false_true H)
| H : _ \/ _ |- _ => destruct H
end
| progress cbv beta zeta in * ].

Definition out_det (eff : SyscallEffect) (m' : Model) (evs : list event)
(o : outcome SyscallEffect) : Prop :=
o = Ok eff m' evs.

Lemma syscall_spec_29 : forall i m o,
bv_unsigned (in_sysno i) = 29%Z ->
syscall_spec i m o <-> ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_56 : forall i m o,
bv_unsigned (in_sysno i) = 56%Z ->
syscall_spec i m o <-> openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_57 : forall i m o,
bv_unsigned (in_sysno i) = 57%Z ->
syscall_spec i m o <-> close_spec (fd32 (in_arg i 0)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_63 : forall i m o,
bv_unsigned (in_sysno i) = 63%Z ->
syscall_spec i m o <-> read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_64 : forall i m o,
bv_unsigned (in_sysno i) = 64%Z ->
syscall_spec i m o <-> write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_66 : forall i m o,
bv_unsigned (in_sysno i) = 66%Z ->
syscall_spec i m o <-> writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_96 : forall i m o,
bv_unsigned (in_sysno i) = 96%Z ->
syscall_spec i m o <-> set_tid_address_spec i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_214 : forall i m o,
bv_unsigned (in_sysno i) = 214%Z ->
syscall_spec i m o <-> brk_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_215 : forall i m o,
bv_unsigned (in_sysno i) = 215%Z ->
syscall_spec i m o <-> munmap_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_222 : forall i m o,
bv_unsigned (in_sysno i) = 222%Z ->
syscall_spec i m o <->
mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_226 : forall i m o,
bv_unsigned (in_sysno i) = 226%Z ->
syscall_spec i m o <-> mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma close_outcome : forall fd i m e o,
fd_lookup (m_fds m) fd = Some e ->
close_spec fd i m o <->
o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds m) fd) m) [].
Proof.
intros fd i m e o Hlk. unfold close_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma ioctl_tty_outcome : forall fd req i m e o,
fd_lookup (m_fds m) fd = Some e ->
e <> FdUrandom ->
tty_only_request req = true ->
ioctl_spec fd req i m o <->
o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [].
Proof.
intros fd req i m e o Hlk Hnd Hreq. unfold ioctl_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *;
destruct e; try (exfalso; apply Hnd; reflexivity); rewrite ?Hreq in *; inv_sys; reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
split; [|reflexivity]. destruct e; try (exfalso; apply Hnd; reflexivity); rewrite ?Hreq; reflexivity.
Qed.

Lemma set_tid_fresh_outcome : forall i m o,
m_tid m = None ->
set_tid_address_spec i m o <->
exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
/\ o = Ok (mkEffect t [] []) (with_tid t m) [].
Proof.
intros i m o Htid. unfold set_tid_address_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys.
eexists; split; [split; eassumption|reflexivity].
- intros (t & Ht & ->). eexists _, _, _, _. split; [reflexivity|]. rewrite Htid.
split; [|reflexivity]. eexists _, _, _, _. split; [exists t; split; [exact Ht|reflexivity]|].
split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma brk_outcome : forall req i m o,
brk_spec req i m o <->
exists r, brk_r_ok m req r = true
/\ o = Ok (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
(brk_unmaps r (vm_brk (m_vmmaps m))) [] [])
(with_brk_next m req r) [].
Proof.
intros req i m o. unfold brk_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
eexists; split; [eassumption|reflexivity].
- intros (r & Hr & ->). eexists _, _, _, _. split; [reflexivity|].
split; [|reflexivity]. eexists _, _, _, _. split; [exists r; split; [exact Hr|reflexivity]|].
split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma munmap_exact_outcome : forall addr len i m o,
(bv_unsigned addr mod page_size = 0)%Z ->
w_is0 len = false ->
(bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE)%Z ->
let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
map_has (vm_maps (m_vmmaps m)) addr n = true ->
munmap_spec addr len i m o <->
o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
(with_mmap_destroyed addr n
(mkVmMapsFull (vm_reserved (m_vmmaps m))
(map_remove (vm_maps (m_vmmaps m)) addr)
(maps_subtract (vm_noaccess (m_vmmaps m))
(bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m) [].
Proof.
intros addr len i m o Hal Hlen Hnw. cbv zeta. intros Hhas. unfold munmap_spec.
rewrite (proj2 (Z.eqb_eq _ _) Hal), Hlen. cbn [negb orb].
sys_unfold. rewrite (proj2 (Z.ltb_ge _ _) Hnw).
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hhas in *; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hhas.
split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|].
split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Definition mmap_err_out (m : Model) (o : outcome SyscallEffect) : Prop :=
exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

Lemma In_mmap_errnos_when : forall c e, In e (mmap_errnos_when c) <-> c = true /\ In e mmap_errnos.
Proof. intros [|] e; cbn [mmap_errnos_when]; split; [intros H; split; [reflexivity| exact H]| intros [_ H]; exact H| intros []| intros [H _]; discriminate H]. Qed.
Lemma In_mprotect_errnos_when : forall c e, In e (mprotect_errnos_when c) <-> c = true /\ In e mprotect_errnos.
Proof. intros [|] e; cbn [mprotect_errnos_when]; split; [intros H; split; [reflexivity| exact H]| intros [_ H]; exact H| intros []| intros [H _]; discriminate H]. Qed.

Lemma mmap_flags_core_bit5 : forall flags : word,
Z.testbit (mmap_flags_core flags) 5 = true -> mmap_anon_b flags = true.
Proof.
intros flags H. unfold mmap_flags_core in H. rewrite Z.ldiff_spec in H.
apply andb_true_iff in H as [H _].
unfold mmap_anon_b, MAP_ANONYMOUS. apply Bool.negb_true_iff. apply Z.eqb_neq.
intros E. pose proof (Z.land_spec (bv_unsigned flags) 32 5) as L.
rewrite E, Z.bits_0, H in L. cbn in L. discriminate L.
Qed.

Lemma w_is0_off_aligned : forall off : word, w_is0 off = true -> mmap_off_aligned_b off = true.
Proof.
intros off H. unfold w_is0 in H. apply bv_eqb_eq in H. subst off. reflexivity.
Qed.

Lemma mmap_modeled_pre : forall prot flags off,
mmap_modeled_b prot flags off = true ->
mmap_off_aligned_b off = true /\ mmap_anon_b flags = true.
Proof.
intros prot flags off H. unfold mmap_modeled_b in H.
apply andb_true_iff in H as [H Hoff]. apply andb_true_iff in H as [_ Hc].
split; [apply w_is0_off_aligned; exact Hoff|].
apply mmap_flags_core_bit5. apply Z.eqb_eq in Hc. rewrite Hc. reflexivity.
Qed.

Lemma mmap_noaccess_pre : forall prot flags off,
mmap_noaccess_b prot flags off = true ->
mmap_off_aligned_b off = true /\ mmap_anon_b flags = true.
Proof.
intros prot flags off H. unfold mmap_noaccess_b in H.
apply andb_true_iff in H as [H Hoff]. apply andb_true_iff in H as [_ Hc].
split; [apply w_is0_off_aligned; exact Hoff|].
apply mmap_flags_core_bit5. apply Z.eqb_eq in Hc. rewrite Hc. reflexivity.
Qed.

Lemma mmap_fixed_noaccess_pre : forall prot flags off,
mmap_fixed_noaccess_b prot flags off = true ->
mmap_off_aligned_b off = true /\ mmap_anon_b flags = true.
Proof.
intros prot flags off H. unfold mmap_fixed_noaccess_b in H.
apply andb_true_iff in H as [H Hoff]. apply andb_true_iff in H as [_ Hc].
split; [apply w_is0_off_aligned; exact Hoff|].
apply mmap_flags_core_bit5. apply Z.eqb_eq in Hc. rewrite Hc. reflexivity.
Qed.

Lemma mmap_rw_outcome_u : forall addr len prot flags fd off i m o,
w_is0 len = false ->
mmap_modeled_b prot flags off = true ->
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
mmap_spec addr len prot flags fd off i m o <->
mmap_err_out m o
\/ exists a, ((bv_unsigned a mod page_size = 0)%Z
/\ (0 < bv_unsigned a)%Z
/\ (bv_unsigned a + nZ <= alloc_top h)%Z
/\ region_free (vm_reserved h ++ vm_maps h) a n = true
/\ mmap_noreserve_backed_ok flags m nZ = true)
/\ o = Ok (mkEffect a [] [(a, n)])
(with_mmap_backing flags a n
(with_vmmaps
(mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
(vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
intros addr len prot flags fd off i m o Hlen Hmod. cbv zeta. unfold mmap_spec.
destruct (mmap_modeled_pre _ _ _ Hmod) as [-> ->]. cbn [negb].
rewrite Hlen, Hmod. unfold mmap_err_out. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
  + left. eexists; split; [eassumption|reflexivity].
  + right. eexists; split; [|reflexivity]. repeat split; assumption.
- intros [(e & He & ->) | (a & Ha & ->)].
  + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
  + right. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noaccess_outcome_u : forall addr len prot flags fd off i m o,
w_is0 len = false ->
mmap_modeled_b prot flags off = false ->
mmap_noaccess_b prot flags off = true ->
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
mmap_spec addr len prot flags fd off i m o <->
mmap_err_out m o
\/ exists a, ((bv_unsigned a mod page_size = 0)%Z
/\ (0 < bv_unsigned a)%Z
/\ (bv_unsigned a + nZ <= alloc_top h)%Z
/\ region_free (vm_reserved h ++ vm_maps h) a n = true)
/\ o = Ok (mkEffectU a [] [] [(a, n)] [] [])
(with_mmap_backing flags a n
(with_vmmaps
(mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
(vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
intros addr len prot flags fd off i m o Hlen Hmod Hna. cbv zeta. unfold mmap_spec.
destruct (mmap_noaccess_pre _ _ _ Hna) as [-> ->]. cbn [negb].
rewrite Hlen, Hmod, Hna. unfold mmap_err_out. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
  + left. eexists; split; [eassumption|reflexivity].
  + right. eexists; split; [|reflexivity]. repeat split; assumption.
- intros [(e & He & ->) | (a & Ha & ->)].
  + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
  + right. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_fixed_noaccess_outcome_u : forall addr len prot flags fd off i m o,
w_is0 len = false ->
mmap_modeled_b prot flags off = false ->
mmap_noaccess_b prot flags off = false ->
mmap_fixed_noaccess_b prot flags off = true ->
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
(bv_unsigned addr + nZ <= alloc_top h)%Z ->
(bv_unsigned addr mod page_size = 0)%Z ->
(0 < bv_unsigned addr)%Z ->
region_free (vm_reserved h) addr n = true ->
map_contains (vm_maps h) addr n = true ->
let o0 := Ok (mkEffectU addr [] [] [(addr, n)] [] [])
(with_mmap_replacement flags addr n
(with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
((addr, n) :: maps_subtract (vm_noaccess h)
(bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [] in
mmap_spec addr len prot flags fd off i m o0
/\ (mmap_spec addr len prot flags fd off i m o ->
o = o0 \/ exists e ws zs us cs cps m' evs, In e mmap_errnos /\ o = Ok (mkEffectU (errno_ret e) ws zs us cs cps) m' evs).
Proof.
intros addr len prot flags fd off i m o Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
pose proof (word_unsigned_range addr) as Har.
unfold mmap_spec. destruct (mmap_fixed_noaccess_pre _ _ _ Hfx) as [-> ->]. cbn [negb].
rewrite Hlen, Hmod, Hna, Hfx. cbv zeta.
assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
{ apply Z.leb_gt. pose proof (alloc_top_room (m_vmmaps m)). unfold stack_max_size in *. lia. }
rewrite E1. sys_unfold.
split.
- eexists _, _, _, _; (split; [reflexivity|]);
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
  Hrf, Hmc; cbn [negb andb]; (split; [|reflexivity]).
  right; left. eexists _, _, _, _. repeat split; reflexivity.
- destruct o as [x m' evs|]; intros H; inv_sys;
  rewrite ?(proj2 (Z.leb_le _ _) Hce), ?(proj2 (Z.eqb_eq _ _) Hal), ?(proj2 (Z.ltb_lt _ _) Hpos),
  ?Hrf, ?Hmc in *; cbn [negb andb] in *; inv_sys;
  first [ left; reflexivity
        | right; do 8 eexists; split; [eassumption| reflexivity] ].
Qed.

Lemma mprotect_expose_outcome_u : forall addr len prot i m o,
mprotect_grows_conflict_b prot = false ->
(bv_unsigned addr mod page_size = 0)%Z ->
w_is0 len = false ->
(bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
mprotect_modeled_b prot = true ->
let h := m_vmmaps m in
let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
map_contains (vm_noaccess h) addr n = true ->
map_contains (vm_maps h) addr n = true ->
mprotect_spec addr len prot i m o <->
(exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
\/ (mprotect_budget_ok m addr n = true
/\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) []).
Proof.
intros addr len prot i m o Hgc Hal Hlen Hnw Hmod. cbv zeta. intros Hna Hma.
unfold mprotect_spec.
rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod. cbn [negb].
sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hna, Hma in *; cbn [andb] in *; inv_sys.
  + left. eexists; split; [eassumption|reflexivity].
  + right. split; [assumption|reflexivity].
- intros [(e & He & ->) | (Hb & ->)]; eexists _, _, _, _; (split; [reflexivity|]);
  rewrite Hna, Hma; cbn [andb]; (split; [|reflexivity]).
  + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
  + right. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma read_dir_outcome : forall fd buf count i m o,
fd_lookup (m_fds m) fd = Some FdDir ->
access_okb buf (bv_unsigned count) = true ->
read_spec fd buf count i m o <->
o = Ok (mkEffect (errno_ret EISDIR) [] []) m [].
Proof.
intros fd buf count i m o Hlk Hacc. unfold read_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, ?Hacc in *; cbn [negb] in *; inv_sys.
reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb]. split; reflexivity.
Qed.

Lemma read_file_outcome : forall fd buf count i m o p off data w,
fd_lookup (m_fds m) fd = Some (FdFile p off) ->
access_okb buf (bv_unsigned count) = true ->
fs_lookup (m_fs m) p = Some data ->
let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
read_bytes_map (in_wmem i) buf (len_word bs) = Some w ->
read_spec fd buf count i m o <->
o = Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
(with_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) m) [].
Proof.
intros fd buf count i m o p off data w Hlk Hacc Hfs. cbv zeta. intros Hw.
unfold read_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, Hacc in *; cbn [negb] in *;
rewrite Hfs in *; cbv zeta in *; rewrite Hw in *; inv_sys; reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb].
rewrite Hfs. cbv zeta. rewrite Hw.
split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Definition open_reads (i : SyscallInput) (pathp : word) : list (word * nat) :=
[(pathp, cstr_access_len_aux (in_mem i) pathp path_max)].

Definition after_copyins (R : list (word * nat)) (body : outcome SyscallEffect -> Prop)
(o : outcome SyscallEffect) : Prop :=
match o with
| Ok eff m' evs => exists core, body (Ok core m' evs)
/\ eff = with_copyins (R ++ eff_copyins core) core
| Unmodeled => body Unmodeled
end.

Lemma record_copyins_iff : forall R (spec : Sys SyscallEffect) i m o,
record_copyins R spec i m o <-> after_copyins R (spec i m) o.
Proof.
intros R spec i m o. unfold record_copyins, after_copyins, bind, pure.
destruct o as [eff m' evs|]; split.
- intros (core & m1 & evs1 & evs2 & Hc & Hp & ->). apply Ok_inj in Hp as (-> & -> & ->).
exists core. rewrite app_nil_r. auto.
- intros (core & Hc & ->). exists core, m', evs, []. rewrite app_nil_r. auto.
- intros [H | (core & m1 & evs1 & _ & Hp)]; [exact H|]. exfalso. exact (Unmodeled_Ok _ _ _ Hp).
- intros H. left. exact H.
Qed.

Lemma after_copyins_det : forall R body r m0 evs0,
(forall o, body o <-> o = Ok (mkEffect r [] []) m0 evs0) ->
forall o, after_copyins R body o <-> o = Ok (with_copyins R (mkEffect r [] [])) m0 evs0.
Proof.
intros R body r m0 evs0 Hb o. unfold after_copyins. destruct o as [eff m' evs|]; split.
- intros (core & Hc & ->). apply Hb in Hc. apply Ok_inj in Hc as (-> & -> & ->).
cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
- intros H. apply Ok_inj in H as (-> & -> & ->). exists (mkEffect r [] []).
split; [apply Hb; reflexivity|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
- intros H. apply Hb in H. exfalso. exact (Unmodeled_Ok _ _ _ H).
- intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

Definition open_res (m : Model) (mk : word -> Model) (o : outcome SyscallEffect) : Prop :=
(exists e, In e openat_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
\/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
/\ o = Ok (mkEffect (alloc_fd (m_fds m)) [] []) (mk (alloc_fd (m_fds m))) []).

Definition open_out (R : list (word * nat)) (m : Model) (mk : word -> Model)
(o : outcome SyscallEffect) : Prop :=
(exists e, In e openat_errnos
/\ o = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) m [])
\/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
/\ o = Ok (with_copyins R (mkEffect (alloc_fd (m_fds m)) [] []))
(mk (alloc_fd (m_fds m))) []).

Lemma open_result_outcome : forall m (mk : word -> Model -> Model) i o,
open_result_spec m mk i m o <-> open_res m (fun fd => mk fd m) o.
Proof.
intros m mk i o. unfold open_result_spec, open_res. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
+ left. eexists; split; [eassumption|reflexivity].
+ right. split; [assumption|reflexivity].
- intros [(e & He & ->) | (Hfree & ->)].
+ left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
+ right. eexists _, _, _, _. split; [eexists; split; [split; [exact Hfree|reflexivity]|reflexivity]|].
split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma after_copyins_open : forall R body m mk,
(forall o, body o <-> open_res m mk o) ->
forall o, after_copyins R body o <-> open_out R m mk o.
Proof.
intros R body m mk Hb o. unfold after_copyins, open_out. destruct o as [eff m' evs|]; split.
- intros (core & Hc & ->). apply Hb in Hc.
destruct Hc as [(e & He & Hc) | (Hfree & Hc)]; apply Ok_inj in Hc as (-> & -> & ->);
cbn [eff_copyins]; rewrite app_nil_r.
+ left. exists e. auto.
+ right. auto.
- intros [(e & He & H) | (Hfree & H)]; apply Ok_inj in H as (-> & -> & ->).
+ exists (mkEffect (errno_ret e) [] []). split; [apply Hb; left; exists e; auto|].
cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
+ exists (mkEffect (alloc_fd (m_fds m)) [] []). split; [apply Hb; right; auto|].
cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
- intros H. apply Hb in H. destruct H as [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
- intros [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
Qed.

Lemma openat_spec_body : forall dirfd pathp flags i m o,
modeled_open_flags flags = true ->
openat_spec dirfd pathp flags i m o <->
after_copyins (open_reads i pathp) (openat_body_spec i m dirfd pathp flags i m) o.
Proof.
intros dirfd pathp flags i m o Hfl. unfold openat_spec.
transitivity (record_copyins (open_reads i pathp) (openat_core_spec dirfd pathp flags) i m o).
{ unfold bind, input, open_reads. destruct o as [eff m' evs|]; split.
- intros (i0 & m1 & evs1 & evs2 & Hi & Hk & ->). apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
- intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
- intros [H | (i0 & m1 & evs1 & Hi & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H)|].
apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
- intros Hk. right. exists i, m, []. split; [reflexivity|exact Hk]. }
rewrite record_copyins_iff.
assert (Hcore : forall o', openat_core_spec dirfd pathp flags i m o' <->
openat_body_spec i m dirfd pathp flags i m o').
{ intros o'. unfold openat_core_spec. rewrite Hfl. cbn [negb].
unfold bind, input, get_model. destruct o' as [eff m' evs|]; split.
- intros (i0 & m1 & evs1 & evs2 & Hi & (m0 & m2 & evs3 & evs4 & Hm & Hb & ->) & ->).
apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
- intros Hb. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
exists m, m, [], evs. split; [reflexivity|]. split; [exact Hb|reflexivity].
- intros [H | (i0 & m1 & evs1 & Hi & [H | (m0 & m2 & evs2 & Hm & Hb)])];
[exfalso; exact (Unmodeled_Ok _ _ _ H)| exfalso; exact (Unmodeled_Ok _ _ _ H)|].
apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
- intros Hb. right. exists i, m, []. split; [reflexivity|]. right.
exists m, m, []. split; [reflexivity|exact Hb]. }
unfold after_copyins. destruct o as [eff m' evs|]; [|apply Hcore].
split; intros (core & Hc & ->); exists core; (split; [apply Hcore; exact Hc|reflexivity]).
Qed.

Lemma err_ret_outcome : forall e i m o,
err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros. unfold err_ret, ret_only, pure. reflexivity. Qed.

Section Openat.
Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
Hypothesis Hfl : modeled_open_flags flags = true.

#[using="Hfl"] Lemma openat_toolong_outcome : forall o,
read_cstr (in_mem i) pathp = CstrTooLong ->
openat_spec dirfd pathp flags i m o <->
o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [].
Proof.
intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
intros o'. unfold openat_body_spec. rewrite Hp. apply err_ret_outcome.
Qed.

#[using="Hfl"] Lemma openat_empty_outcome : forall o,
read_cstr (in_mem i) pathp = CstrOk [] ->
openat_spec dirfd pathp flags i m o <->
o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
Proof.
intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
intros o'. unfold openat_body_spec. rewrite Hp. cbn [path_eqb]. apply err_ret_outcome.
Qed.

Hypothesis Hdir : dirfd = AT_FDCWD32.
Hypothesis Hrd : Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z.

#[using="Hdir Hrd"] Lemma openat_body_resolved : forall p o,
read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
openat_body_spec i m dirfd pathp flags i m o <-> openat_read_spec p m i m o.
Proof.
intros p o Hp Hne Hsl. unfold openat_body_spec. rewrite Hp.
replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec. rewrite Hsl, Hrd.
reflexivity.
Qed.

#[using="Hfl Hdir Hrd"] Lemma openat_absent_outcome : forall p o,
read_cstr (in_mem i) pathp = CstrOk p -> p <> [] ->
path_is_dirref p = false -> path_has_slash p = false ->
fs_lookup (m_fs m) p = None ->
openat_spec dirfd pathp flags i m o <->
o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
Proof.
intros p o Hp Hne Hnd Hsl Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
rewrite Hnd, Hfs. apply err_ret_outcome.
Qed.

#[using="Hfl Hdir Hrd"] Lemma openat_dirref_outcome : forall p o,
read_cstr (in_mem i) pathp = CstrOk p -> path_is_dirref p = true ->
openat_spec dirfd pathp flags i m o <->
open_out (open_reads i pathp) m (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m) o.
Proof.
intros p o Hp Hdr. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
assert (Hne : p <> []).
{ intros ->. cbv in Hdr. discriminate Hdr. }
intros o'. rewrite (openat_body_resolved p o' Hp Hne (path_is_dirref_no_slash _ Hdr)).
unfold openat_read_spec. rewrite Hdr. apply open_result_outcome.
Qed.

#[using="Hfl Hdir Hrd"] Lemma openat_dot_outcome : forall o,
read_cstr (in_mem i) pathp = CstrOk dot_path ->
openat_spec dirfd pathp flags i m o <->
open_out (open_reads i pathp) m (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m) o.
Proof. intros o Hp. apply (openat_dirref_outcome dot_path o Hp). reflexivity. Qed.

#[using="Hfl Hdir Hrd"] Lemma openat_file_outcome : forall p d o,
read_cstr (in_mem i) pathp = CstrOk p -> p <> [] ->
path_is_dirref p = false -> path_has_slash p = false ->
fs_lookup (m_fs m) p = Some d ->
openat_spec dirfd pathp flags i m o <->
open_out (open_reads i pathp) m
(fun fd => with_fds (fd_insert (m_fds m) fd (FdFile p (Z_to_bv 64 0))) m) o.
Proof.
intros p d o Hp Hne Hnd Hsl Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
rewrite Hnd, Hfs. apply open_result_outcome.
Qed.
End Openat.

Lemma cap_iovecs_aux_id : forall iovs left,
(iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned, IH by lia. reflexivity.
Qed.

Definition node_rw_max : Z := 67108864%Z.

Lemma cap_iovecs_id_rw : forall iovs,
(iovs_total iovs <= node_rw_max)%Z -> cap_iovecs iovs = iovs.
Proof.
intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id.
unfold MAX_RW_COUNT. unfold node_rw_max in H. lia.
Qed.

Lemma gather_prefix_total0 : forall mp iovs,
iovs_total iovs = 0%Z -> gather_prefix mp iovs = [].
Proof.
intros mp iovs; induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
cbn [iovs_total] in H. pose proof (iovs_total_nonneg r). pose proof (word_unsigned_range n).
assert (Hn : bv_unsigned n = 0%Z) by lia.
cbn [gather_prefix]. rewrite readable_bytes_eq. unfold word_to_nat. rewrite Hn.
cbn [Z.to_nat readable_bytes_aux length Z.of_nat Z.eqb app]. apply IH. lia.
Qed.

Lemma bind_input_model : forall (k : SyscallInput -> Model -> Sys SyscallEffect) i m o,
(bind input (fun i0 => bind get_model (fun m0 => k i0 m0))) i m o <-> k i m i m o.
Proof.
intros k i m o. unfold bind, input, get_model. destruct o as [eff m' evs|]; split.
- intros (i0 & m1 & e1 & e2 & Hi & (m0 & m2 & e3 & e4 & Hm & Hk & ->) & ->).
apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
- intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
exists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
- intros [H | (i0 & m1 & e1 & Hi & [H | (m0 & m2 & e2 & Hm & Hk)])];
[exfalso; exact (Unmodeled_Ok _ _ _ H) | exfalso; exact (Unmodeled_Ok _ _ _ H) |].
apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
- intros Hk. right. exists i, m, []. split; [reflexivity|]. right.
exists m, m, []. split; [reflexivity| exact Hk].
Qed.

Lemma writev_chan_outcome : forall fd iov iovcnt i m o ch iovs bs,
fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
w_is0 ch = false ->
import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
(iovs_total iovs <= node_rw_max)%Z ->
gather_iovecs (in_mem i) iovs = Some bs ->
(1 <= Z.of_nat (length bs))%Z ->
let CA := import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) in
writev_spec fd iov iovcnt i m o <->
exists k, (1 <= k <= length bs)%nat /\
o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
m (map (WriteEv ch) (firstn k bs)).
Proof.
intros fd iov iovcnt i m o ch iovs bs Hfd Hch Himp Htot Hg Hbs1.
cbv zeta.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
pose proof (cap_iovecs_id_rw _ Htot) as Hcap.
assert (Herrk : forall k, (k <= length bs)%nat ->
addr_is_error_b (len_word (firstn k bs)) = false).
{ intros k Hk. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
rewrite len_word_unsigned by (rewrite firstn_length_le by lia; unfold two_pow_64;
unfold node_rw_max in Htot; lia).
rewrite firstn_length_le by lia. unfold node_rw_max in Htot. lia. }
unfold writev_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
rewrite Hfd, Hch. cbv iota. rewrite Himp. cbv iota zeta.
unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (addr_is_error_b (len_word bs)) with false
by (symmetry; rewrite <- (firstn_all bs); rewrite (Herrk (length bs)) by lia; reflexivity).
cbv iota. unfold writev_buf_gap. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
match goal with Hds : ?ds = firstn (length ?ds) bs |- _ =>
exists (length ds); rewrite <- Hds;
assert (Hk : (length ds <= length bs)%nat)
by (rewrite Hds; rewrite length_firstn; apply Nat.le_min_r)
end.
split; [lia|]. rewrite !app_nil_r. unfold len_word. reflexivity.
- intros (k & Hk & ->).
assert (Hlk : length (firstn k bs) = k) by (apply firstn_length_le; lia).
eexists _, _, _, _. split.
+ eexists _, _, _, _. split.
* exists (firstn k bs). split; [|reflexivity].
rewrite Hlk. split; [lia|]. split; [unfold two_pow_64, node_rw_max in *; lia|].
split; [apply Herrk; lia|reflexivity].
* split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
+ rewrite Hlk, !app_nil_r. unfold len_word. rewrite Hlk. split; reflexivity.
Qed.

Lemma writev_chan_zero_outcome : forall fd iov iovcnt i m o ch iovs,
fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
w_is0 ch = false ->
import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
iovs_total iovs = 0%Z ->
writev_spec fd iov iovcnt i m o <->
o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
(mkEffect (Z_to_bv 64 0) [] [])) m [].
Proof.
intros fd iov iovcnt i m o ch iovs Hfd Hch Himp Htot.
assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_rw; unfold node_rw_max; lia).
unfold writev_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
rewrite Hfd, Hch. cbv iota. rewrite Himp. cbv iota zeta.
rewrite Hcap, Htot. cbn [Z.eqb].
rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.

Lemma exit_outcome : forall code i m o,
exit_spec code i m o <->
o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [].
Proof.
intros code i m o. unfold exit_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma syscall_spec_93 : forall i m o,
bv_unsigned (in_sysno i) = 93%Z ->
syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_94 : forall i m o,
bv_unsigned (in_sysno i) = 94%Z ->
syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma set_tid_known_outcome : forall i m o t0,
m_tid m = Some t0 ->
set_tid_address_spec i m o <-> o = Ok (mkEffect t0 [] []) m [].
Proof.
intros i m o t0 Htid. unfold set_tid_address_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Htid. split; reflexivity.
Qed.

Lemma close_ebadf_outcome : forall fd i m o,
fd_lookup (m_fds m) fd = None ->
close_spec fd i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
intros fd i m o Hlk. unfold close_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma read_ebadf_outcome : forall fd buf count i m o,
fd_lookup (m_fds m) fd = None ->
read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
intros fd buf count i m o Hlk. unfold read_spec. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Definition munmap_out (addr len : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len
then o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
else if (TASK_SIZE <? bv_unsigned addr + nZ)%Z then o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
else if map_has (vm_maps h) addr n then
o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
(with_mmap_destroyed addr n
(mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) addr)
(maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m) []
else if munmap_free_ok h addr nZ then o = Ok (mkEffect (Z_to_bv 64 0) [] []) m []
else o = Unmodeled.

Lemma munmap_outcome : forall addr len i m o,
munmap_spec addr len i m o <-> munmap_out addr len m o.
Proof.
intros addr len i m o. unfold munmap_spec, munmap_out. cbv zeta.
destruct (negb (bv_unsigned addr mod page_size =? 0)%Z || w_is0 len).
{ apply err_ret_outcome. }
destruct (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z eqn:Hwrap;
destruct (map_has (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hhas;
destruct (munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len))) eqn:Hfree;
sys_unfold; split;
first [ destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hwrap, ?Hhas, ?Hfree in *; inv_sys; reflexivity
| intros ->;
first [ eexists _, _, _, _; split; [reflexivity|]; rewrite ?Hwrap, ?Hhas, ?Hfree;
first [ split; reflexivity
| split; [|reflexivity]; eexists _, _, _, _; split; [reflexivity|];
split; [|reflexivity]; eexists _, _, _, _; repeat split; reflexivity ]
| right; eexists _, _, _; split; [reflexivity|]; rewrite ?Hwrap, ?Hhas, ?Hfree; reflexivity ] ].
Qed.

Lemma write_chan_outcome : forall fd buf count i m o ch bs,
fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
w_is0 ch = false ->
read_bytes_map (in_mem i) buf count = Some bs ->
bv_unsigned count = Z.of_nat (length bs) ->
(1 <= Z.of_nat (length bs) <= rw_bytes_max)%Z ->
write_spec fd buf count i m o <->
exists k, (1 <= k <= length bs)%nat /\
o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] [(buf, k)])
m (map (WriteEv ch) (firstn k bs)).
Proof.
intros fd buf count i m o ch bs Hfd Hch Hrd Hcnt Hlen.
unfold write_spec.
rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
rewrite Hfd, Hch.
rewrite rw_range_in_range by lia.
assert (Hc0 : w_is0 count = false).
{ unfold w_is0, bv_eqb. rewrite Hcnt. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
rewrite Hc0. cbv zeta.
rewrite write_source_of_rw by lia.
rewrite (readable_bytes_full _ _ _ _ Hrd).
replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
rewrite rw_count_clamp_of_rw by lia.
sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
match goal with Hds : ?ds = firstn (length ?ds) bs |- _ =>
exists (length ds); rewrite <- Hds;
assert (Hk : (length ds <= length bs)%nat)
by (rewrite Hds; rewrite length_firstn; apply Nat.le_min_r)
end.
split; [lia|]. rewrite !app_nil_r. unfold len_word. reflexivity.
- intros (k & Hk & ->).
assert (Hlk : length (firstn k bs) = k) by (apply firstn_length_le; lia).
exists (firstn k bs), m, [], (map (WriteEv ch) (firstn k bs)). split.
+ exists (firstn k bs). split; [|reflexivity]. rewrite Hlk. split; [lia|]. split; [lia|reflexivity].
+ split; [|reflexivity].
eexists _, _, _, _. split; [reflexivity|]. split; [|symmetry; apply app_nil_r].
eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins app].
unfold len_word. rewrite Hlk. reflexivity.
Qed.

Lemma writev_chan_cnt0_outcome : forall fd iov iovcnt i m o ch,
fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
w_is0 ch = false ->
w_is0 (iovcnt32 iovcnt) = true ->
writev_spec fd iov iovcnt i m o <-> o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [].
Proof.
intros fd iov iovcnt i m o ch Hfd Hch Hcnt0.
unfold w_is0 in Hcnt0. apply bv_eqb_eq in Hcnt0.
unfold writev_spec.
rewrite (bind_input_model (fun i0 m0 => _)). cbv beta. rewrite Hfd, Hch, Hcnt0.
unfold import_iovecs_accesses, import_iovecs.
replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 1)) with false by reflexivity.
rewrite bv_eqb_refl. cbn [cap_iovecs cap_iovecs_aux iovs_total Z.eqb].
rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.

Definition mprotect_out (addr len prot : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
if mprotect_grows_conflict_b prot then o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
else if w_is0 len then o = Ok (mkEffect (Z_to_bv 64 0) [] []) m []
else if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
else if mprotect_modeled_b prot then
if map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n then
(mprotect_refusable m addr n = true
/\ exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
\/ (mprotect_budget_ok m addr n = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) [])
else if map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n then
o = Ok (mkEffect (Z_to_bv 64 0) [] []) m []
else o = Unmodeled
else o = Unmodeled.

Definition mprotect_out_u (addr len prot : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
if mprotect_grows_conflict_b prot then o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
else if w_is0 len then o = Ok (mkEffect (Z_to_bv 64 0) [] []) m []
else if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
else if mprotect_modeled_b prot then
if map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n then
(exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
\/ (mprotect_budget_ok m addr n = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) [])
else if map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n then
o = Ok (mkEffect (Z_to_bv 64 0) [] []) m []
else o = Unmodeled
else o = Unmodeled.

Lemma mprotect_outcome_u : forall addr len prot i m o,
mprotect_spec addr len prot i m o <-> mprotect_out_u addr len prot m o.
Proof.
intros addr len prot i m o. unfold mprotect_spec, mprotect_out_u. cbv zeta.
destruct (mprotect_grows_conflict_b prot); [apply err_ret_outcome|].
destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [apply err_ret_outcome|].
destruct (w_is0 len); [unfold ret_only, pure; reflexivity|].
destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z; [apply err_ret_outcome|].
destruct (mprotect_modeled_b prot); [| unfold unmodeled; reflexivity].
destruct (map_contains (vm_noaccess (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) &&
map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hc;
destruct (map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) &&
region_free (vm_noaccess (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hf;
sys_unfold; split.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hc in *; inv_sys.
  + left. eexists; split; [eassumption| reflexivity].
  + right. split; [assumption| reflexivity].
- intros [(e & He & ->) | (Hb & ->)]; eexists _, _, _, _; (split; [reflexivity|]); rewrite Hc; (split; [|reflexivity]).
  + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
  + right. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hc in *; inv_sys.
  + left. eexists; split; [eassumption| reflexivity].
  + right. split; [assumption| reflexivity].
- intros [(e & He & ->) | (Hb & ->)]; eexists _, _, _, _; (split; [reflexivity|]); rewrite Hc; (split; [|reflexivity]).
  + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
  + right. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hc, ?Hf in *; inv_sys. reflexivity.
- intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hc, Hf. split; reflexivity.
- destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hc, ?Hf in *; inv_sys. reflexivity.
- intros ->. right. eexists _, _, _. split; [reflexivity|]. rewrite Hc, Hf. reflexivity.
Qed.

Definition iind {A} (s : Sys A) : Prop := forall i i' m o, s i m o -> s i' m o.

Lemma iind_pure {A} (x : A) : iind (pure x). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_unmodeled {A} : iind (@unmodeled A). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_get_model : iind get_model. Proof. intros i i' m o H; exact H. Qed.
Lemma iind_get_vmmaps : iind get_vmmaps. Proof. intros i i' m o H; exact H. Qed.
Lemma iind_get_fds : iind get_fds. Proof. intros i i' m o H; exact H. Qed.
Lemma iind_modify f : iind (modify f). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_choose {A} (P : A -> Prop) : iind (choose P). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_emit evs : iind (emit evs). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_errno_from l : iind (errno_from l). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_ret_only r : iind (ret_only r). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_err_ret e : iind (err_ret e). Proof. intros i i' m o H; exact H. Qed.
Lemma iind_bind {A B} (s : Sys A) (k : A -> Sys B) :
iind s -> (forall x, iind (k x)) -> iind (bind s k).
Proof.
intros Hs Hk i i' m o. unfold bind. destruct o as [x m' e|].
- intros (x0 & m0 & e1 & e2 & H1 & H2 & ->). exists x0, m0, e1, e2.
split; [exact (Hs _ _ _ _ H1)|]. split; [exact (Hk _ _ _ _ _ H2)| reflexivity].
- intros [H | (x0 & m0 & e1 & H1 & H2)].
+ left. exact (Hs _ _ _ _ H).
+ right. exists x0, m0, e1. split; [exact (Hs _ _ _ _ H1)| exact (Hk _ _ _ _ _ H2)].
Qed.
Lemma iind_alt {A} (a b : Sys A) : iind a -> iind b -> iind (alt a b).
Proof. intros Ha Hb i i' m o [H|H]; [left; exact (Ha _ _ _ _ H)| right; exact (Hb _ _ _ _ H)]. Qed.
Ltac iind_tac :=
lazymatch goal with
| |- iind (bind _ _) => apply iind_bind; [iind_tac | intros ?; iind_tac]
| |- iind (alt _ _) => apply iind_alt; iind_tac
| |- iind (match ?b with true => _ | false => _ end) => destruct b; iind_tac
| |- iind (match ?x with _ => _ end) => destruct x; iind_tac
| |- iind ?s =>
first [ apply iind_pure | apply iind_unmodeled | apply iind_get_model | apply iind_get_vmmaps
| apply iind_get_fds | apply iind_modify | apply iind_choose | apply iind_emit
| apply iind_errno_from | apply iind_ret_only | apply iind_err_ret
| let h := (lazymatch s with ?f _ _ _ _ _ _ => f | ?f _ _ _ _ _ => f | ?f _ _ _ _ => f | ?f _ _ _ => f | ?f _ _ => f | ?f _ => f | ?f => f end) in
progress unfold h; cbv zeta; iind_tac
| fail 2 "iind_tac: stuck on" s ]
end.

Lemma brk_iind : forall req, iind (brk_spec req).
Proof. intros. iind_tac. Qed.
Lemma munmap_iind : forall a l, iind (munmap_spec a l).
Proof. intros. iind_tac. Qed.
Lemma mprotect_iind : forall a l p, iind (mprotect_spec a l p).
Proof. intros. iind_tac. Qed.
Lemma mmap_iind : forall a l p f fd off, iind (mmap_spec a l p f fd off).
Proof. intros. iind_tac. Qed.

Definition vm_only (m m' : Model) : Prop :=
m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\
m_lim m' = m_lim m /\ m_time m' = m_time m /\
(m_vm_lazy m = [] -> m_vm_lazy m' = []).

Lemma vm_only_refl : forall m, vm_only m m.
Proof. intros m. repeat split; auto. Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
intros a b c (?&?&?&?&?&?&Hl1) (?&?&?&?&?&?&Hl2). unfold vm_only.
repeat split; try congruence. auto.
Qed.
Lemma vm_only_with_vmmaps : forall m X h, vm_only m X -> vm_only m (with_vmmaps h X).
Proof.
intros m X h (?&?&?&?&?&?&Hl). unfold vm_only, with_vmmaps, m_vm_lazy in *; cbn. repeat split; auto.
Qed.
Lemma maps_subtract_nil : forall lo hi, maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.
Lemma vm_only_with_vm_backing : forall m X lazy mat,
vm_only m X -> (m_vm_lazy X = [] -> lazy = []) -> vm_only m (with_vm_backing lazy mat X).
Proof.
intros m X lazy mat (?&?&?&?&?&?&Hl) Hz. unfold vm_only, with_vm_backing in *. unfold m_vm_lazy at 2. cbn.
repeat split; auto.
Qed.
Lemma vm_only_forget_range : forall m X lo hi, vm_only m X -> vm_only m (vm_forget_range lo hi X).
Proof.
intros m X lo hi H. unfold vm_forget_range. apply vm_only_with_vm_backing; [exact H|].
intros ->. reflexivity.
Qed.
Lemma vm_only_forget_ranges : forall rs m X, vm_only m X -> vm_only m (forget_vm_ranges rs X).
Proof.
induction rs as [|[a n] rs IH]; intros m X H; cbn [forget_vm_ranges]; [exact H|].
apply IH. apply vm_only_forget_range. exact H.
Qed.
Lemma vm_only_brk_next : forall m X req r, vm_only m X -> vm_only m (with_brk_next X req r).
Proof. intros. unfold with_brk_next. apply vm_only_forget_ranges, vm_only_with_vmmaps. assumption. Qed.
Lemma vm_only_mmap_backing : forall m X flags a n,
mmap_noreserve_b flags = false -> vm_only m X -> vm_only m (with_mmap_backing flags a n X).
Proof. intros m X flags a n Hf H. unfold with_mmap_backing. rewrite Hf. exact H. Qed.
Lemma vm_only_mmap_replacement : forall m X flags a n,
mmap_noreserve_b flags = false -> vm_only m X -> vm_only m (with_mmap_replacement flags a n X).
Proof. intros. unfold with_mmap_replacement. apply vm_only_mmap_backing; [assumption|]. apply vm_only_forget_range. assumption. Qed.
Lemma vm_only_mmap_destroyed : forall m X a n h, vm_only m X -> vm_only m (with_mmap_destroyed a n h X).
Proof. intros. unfold with_mmap_destroyed. apply vm_only_forget_range, vm_only_with_vmmaps. assumption. Qed.
Lemma vm_only_mprotect_next : forall m X a n, vm_only m X -> vm_only m (mprotect_model_next X a n).
Proof. intros. unfold mprotect_model_next. apply vm_only_with_vmmaps. assumption. Qed.

Ltac vm_only_tac :=
repeat first [ apply vm_only_refl
| apply vm_only_with_vmmaps | apply vm_only_forget_range | apply vm_only_forget_ranges
| apply vm_only_brk_next | apply vm_only_mmap_destroyed | apply vm_only_mprotect_next
| apply vm_only_mmap_backing; [assumption|]
| apply vm_only_mmap_replacement; [assumption|] ].

Definition SP {A} (m0 : Model) (s : Sys A) : Prop :=
forall i x m' evs, s i m0 (Ok x m' evs) -> evs = [] /\ vm_only m0 m'.

Lemma SP_pure {A} m0 (x : A) : SP m0 (pure x).
Proof. intros i y m' evs H. unfold pure in H. injection H as ? ? ?; subst. split; [reflexivity| apply vm_only_refl]. Qed.
Lemma SP_ret_only m0 r : SP m0 (ret_only r). Proof. apply SP_pure. Qed.
Lemma SP_err_ret m0 e : SP m0 (err_ret e). Proof. apply SP_pure. Qed.
Lemma SP_unmodeled {A} m0 : SP m0 (@unmodeled A). Proof. intros i y m' evs H. discriminate H. Qed.
Lemma SP_modify m0 F : vm_only m0 (F m0) -> SP m0 (modify F).
Proof. intros HF i y m' evs H. unfold modify in H. injection H as ? ? ?; subst. split; [reflexivity| exact HF]. Qed.

Lemma SP_bind {A B} m0 (s : Sys A) (k : A -> Sys B) :
(forall i x m1 e1, s i m0 (Ok x m1 e1) -> e1 = [] /\ SP m1 (k x) /\ vm_only m0 m1) -> SP m0 (bind s k).
Proof.
intros H i y m' evs Hb. unfold bind in Hb. destruct Hb as (x & m1 & e1 & e2 & H1 & H2 & ->).
destruct (H _ _ _ _ H1) as (-> & Hk & Hv). destruct (Hk _ _ _ _ H2) as (-> & Hv2).
split; [reflexivity|]. eapply vm_only_trans; eassumption.
Qed.
Lemma SP_bind_get_model {B} m0 (k : Model -> Sys B) : SP m0 (k m0) -> SP m0 (bind get_model k).
Proof. intros H. apply SP_bind. intros i x m1 e1 E. unfold get_model in E. injection E as ? ? ?; subst. split; [reflexivity|]. split; [exact H| apply vm_only_refl]. Qed.
Lemma SP_bind_get_vmmaps {B} m0 (k : VmMaps -> Sys B) : SP m0 (k (m_vmmaps m0)) -> SP m0 (bind get_vmmaps k).
Proof. intros H. apply SP_bind. intros i x m1 e1 E. unfold get_vmmaps in E. injection E as ? ? ?; subst. split; [reflexivity|]. split; [exact H| apply vm_only_refl]. Qed.
Lemma SP_bind_choose {A B} m0 (P : A -> Prop) (k : A -> Sys B) : (forall x, P x -> SP m0 (k x)) -> SP m0 (bind (choose P) k).
Proof. intros H. apply SP_bind. intros i x m1 e1 E. unfold choose in E. destruct E as (y & Py & E). injection E as ? ? ?; subst. split; [reflexivity|]. split; [apply H; exact Py| apply vm_only_refl]. Qed.
Lemma SP_bind_errno_from {B} m0 l (k : Z -> Sys B) : (forall e, SP m0 (k e)) -> SP m0 (bind (errno_from l) k).
Proof. intros H. apply SP_bind. intros i x m1 e1 E. unfold errno_from, choose in E. destruct E as (y & Py & E). injection E as ? ? ?; subst. split; [reflexivity|]. split; [apply H| apply vm_only_refl]. Qed.
Lemma SP_bind_modify {B} m0 F (k : unit -> Sys B) : vm_only m0 (F m0) -> SP (F m0) (k tt) -> SP m0 (bind (modify F) k).
Proof. intros HF H. apply SP_bind. intros i x m1 e1 E. unfold modify in E. injection E as ? ? ?; subst. split; [reflexivity|]. split; [exact H| exact HF]. Qed.
Lemma SP_alt {A} m0 (a b : Sys A) : SP m0 a -> SP m0 b -> SP m0 (alt a b).
Proof. intros Ha Hb i x m' evs [H|H]; [apply (Ha _ _ _ _ H)| apply (Hb _ _ _ _ H)]. Qed.
Ltac sp_head s :=
lazymatch s with ?f _ _ _ _ _ _ _ => f | ?f _ _ _ _ _ _ => f | ?f _ _ _ _ _ => f | ?f _ _ _ _ => f | ?f _ _ _ => f | ?f _ _ => f | ?f _ => f | ?f => f end.

Ltac sp_tac :=
cbv beta zeta;
lazymatch goal with
| |- SP _ (bind get_model _) => apply SP_bind_get_model; sp_tac
| |- SP _ (bind get_vmmaps _) => apply SP_bind_get_vmmaps; sp_tac
| |- SP _ (bind (choose _) _) => apply SP_bind_choose; intros ? ?; sp_tac
| |- SP _ (bind (errno_from _) _) => apply SP_bind_errno_from; intros ?; sp_tac
| |- SP _ (bind (modify _) _) => apply SP_bind_modify; [vm_only_tac | sp_tac]
| |- SP _ (bind ?s _) => let h := sp_head s in progress unfold h; sp_tac
| |- SP _ (alt _ _) => apply SP_alt; sp_tac
| |- SP _ (match ?b with true => _ | false => _ end) => destruct b eqn:?; sp_tac
| |- SP _ (match ?x with _ => _ end) => destruct x eqn:?; sp_tac
| |- SP _ (pure _) => apply SP_pure
| |- SP _ (ret_only _) => apply SP_ret_only
| |- SP _ (err_ret _) => apply SP_err_ret
| |- SP _ unmodeled => apply SP_unmodeled
| |- SP _ (modify _) => apply SP_modify; vm_only_tac
| |- SP _ ?s => let h := sp_head s in first [progress unfold h; sp_tac | fail 2 "sp_tac stuck:" s]
end.

Lemma brk_sp : forall req m0, SP m0 (brk_spec req).
Proof. intros. sp_tac. Qed.
Lemma munmap_sp : forall a l m0, SP m0 (munmap_spec a l).
Proof. intros. sp_tac. Qed.
Lemma mprotect_sp : forall a l p m0, SP m0 (mprotect_spec a l p).
Proof. intros. sp_tac. Qed.
Lemma mmap_sp : forall a l p f fd off m0, mmap_noreserve_b f = false -> SP m0 (mmap_spec a l p f fd off).
Proof. intros. sp_tac. Qed.

Definition TOT {A} (m : Model) (s : Sys A) : Prop :=
forall i, (exists x m' e, s i m (Ok x m' e)) \/ s i m Unmodeled.

Lemma TOT_pure {A} m (x : A) : TOT m (pure x).
Proof. intros i. left. exists x, m, []. reflexivity. Qed.
Lemma TOT_ret_only m r : TOT m (ret_only r). Proof. apply TOT_pure. Qed.
Lemma TOT_err_ret m e : TOT m (err_ret e). Proof. apply TOT_pure. Qed.
Lemma TOT_unmodeled {A} m : TOT m (@unmodeled A). Proof. intros i. right. reflexivity. Qed.
Lemma TOT_modify m f : TOT m (modify f). Proof. intros i. left. exists tt, (f m), []. reflexivity. Qed.
Lemma TOT_bind {A B} m (s : Sys A) (k : A -> Sys B) :
(forall i, (exists x m' e, s i m (Ok x m' e) /\ TOT m' (k x)) \/ s i m Unmodeled) -> TOT m (bind s k).
Proof.
intros H i. unfold bind. destruct (H i) as [(x & m' & e & Hs & Hk)|Hs].
- destruct (Hk i) as [(y & m'' & e' & Hy)|Hy].
+ left. exists y, m'', (e ++ e'). exists x, m', e, e'. auto.
+ right. right. exists x, m', e. auto.
- right. left. exact Hs.
Qed.
Lemma TOT_bind_get_model {B} m (k : Model -> Sys B) : TOT m (k m) -> TOT m (bind get_model k).
Proof. intros H. apply TOT_bind. intros i. left. exists m, m, []. split; [reflexivity| exact H]. Qed.
Lemma TOT_bind_get_vmmaps {B} m (k : VmMaps -> Sys B) : TOT m (k (m_vmmaps m)) -> TOT m (bind get_vmmaps k).
Proof. intros H. apply TOT_bind. intros i. left. exists (m_vmmaps m), m, []. split; [reflexivity| exact H]. Qed.
Lemma TOT_bind_modify {B} m f (k : unit -> Sys B) : TOT (f m) (k tt) -> TOT m (bind (modify f) k).
Proof. intros H. apply TOT_bind. intros i. left. exists tt, (f m), []. split; [reflexivity| exact H]. Qed.
Lemma TOT_bind_choose {A B} m (P : A -> Prop) (k : A -> Sys B) x : P x -> TOT m (k x) -> TOT m (bind (choose P) k).
Proof. intros HP H. apply TOT_bind. intros i. left. exists x, m, []. split; [| exact H]. exists x. auto. Qed.
Lemma TOT_bind_errno_from {B} m l (k : Z -> Sys B) e : In e l -> TOT m (k e) -> TOT m (bind (errno_from l) k).
Proof. intros He H. unfold errno_from. apply (TOT_bind_choose m _ k e He H). Qed.
Lemma TOT_alt_l {A} m (a b : Sys A) : TOT m a -> TOT m (alt a b).
Proof. intros H i. destruct (H i) as [(x & m' & e & Hx)|Hx]; [left; exists x, m', e; left; exact Hx| right; left; exact Hx]. Qed.
Lemma TOT_alt_r {A} m (a b : Sys A) : TOT m b -> TOT m (alt a b).
Proof. intros H i. destruct (H i) as [(x & m' & e & Hx)|Hx]; [left; exists x, m', e; right; exact Hx| right; right; exact Hx]. Qed.
Create HintDb tot_witness.

Lemma TOT_bind_choose_ex {A B} m (P : A -> Prop) (k : A -> Sys B) :
(exists x, P x) -> (forall x, P x -> TOT m (k x)) -> TOT m (bind (choose P) k).
Proof. intros [x HP] H. exact (TOT_bind_choose m P k x HP (H x HP)). Qed.

Lemma grant_witness : forall flags m nZ, mmap_grant_refusable flags m nZ = false ->
exists a : word, (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
/\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
/\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true
/\ mmap_noreserve_backed_ok flags m nZ = true.
Proof.
intros flags m nZ H. unfold mmap_grant_refusable in H. apply orb_false_elim in H as [Hb Hg].
apply negb_false_iff in Hb, Hg. apply vm_gap_available_iff in Hg as (a & H1 & H2 & H3 & H4).
exists a. repeat split; assumption.
Qed.
Lemma reserve_witness : forall m nZ, mmap_reserve_refusable m nZ = false ->
exists a : word, (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
/\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
/\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
intros m nZ H. unfold mmap_reserve_refusable in H. apply negb_false_iff in H.
apply vm_gap_available_iff in H. exact H.
Qed.
Lemma fresh_witness : forall flags m nZ (addr : word), mmap_fixed_fresh_refusable flags m nZ = false ->
addr = addr /\ mmap_noreserve_backed_ok flags m nZ = true.
Proof. intros flags m nZ addr H. unfold mmap_fixed_fresh_refusable in H. apply negb_false_iff in H. split; [reflexivity| exact H]. Qed.
Lemma commit_witness : forall flags m addr n, mmap_fixed_commit_refusable flags m addr n = false -> mmap_fixed_rw_budget_ok flags m addr n = true.
Proof. intros flags m addr n H. unfold mmap_fixed_commit_refusable in H. apply negb_false_iff in H. exact H. Qed.
Lemma span_witness : forall flags m addr n, mmap_fixed_span_refusable flags m addr n = false -> mmap_fixed_rw_span_budget_ok flags m addr n = true.
Proof. intros flags m addr n H. unfold mmap_fixed_span_refusable in H. apply negb_false_iff in H. exact H. Qed.
Lemma mprotect_witness : forall m addr n, mprotect_refusable m addr n = false -> mprotect_budget_ok m addr n = true.
Proof. intros m addr n H. unfold mprotect_refusable in H. apply negb_false_iff in H. exact H. Qed.
#[export] Hint Resolve fresh_witness commit_witness span_witness mprotect_witness : tot_witness.
#[export] Hint Extern 1 (?a = ?a) => reflexivity : tot_witness.

Ltac tot_tac :=
cbv beta zeta;
lazymatch goal with
| |- TOT _ (bind get_model _) => apply TOT_bind_get_model; tot_tac
| |- TOT _ (bind get_vmmaps _) => apply TOT_bind_get_vmmaps; tot_tac
| |- TOT _ (bind (errno_from _) _) => eapply TOT_bind_errno_from; [left; reflexivity | tot_tac]
| |- TOT _ (bind (choose (fun _ : unit => _)) _) => eapply (TOT_bind_choose _ _ _ tt); [solve [eauto with tot_witness] | tot_tac]
| |- TOT _ (bind (choose _) _) =>
first [ eapply TOT_bind_choose; [solve [eauto with tot_witness] | tot_tac]
| apply TOT_bind_choose_ex; [solve [eauto using grant_witness, reserve_witness] | intros ? ?; tot_tac] ]
| |- TOT _ (bind (modify _) _) => apply TOT_bind_modify; tot_tac
| |- TOT _ (bind ?s _) => let h := sp_head s in progress unfold h; tot_tac
| |- TOT _ (alt _ _) => first [apply TOT_alt_l; tot_tac | apply TOT_alt_r; tot_tac]
| |- TOT _ (match ?b with true => _ | false => _ end) => destruct b eqn:?; tot_tac
| |- TOT _ (match ?x with _ => _ end) => destruct x eqn:?; tot_tac
| |- TOT _ (pure _) => apply TOT_pure
| |- TOT _ (ret_only _) => apply TOT_ret_only
| |- TOT _ (err_ret _) => apply TOT_err_ret
| |- TOT _ unmodeled => apply TOT_unmodeled
| |- TOT _ (modify _) => apply TOT_modify
| |- TOT _ ?s => let h := sp_head s in first [progress unfold h; tot_tac | fail 2 "tot_tac stuck:" s]
end.

Lemma brk_r_ok_same : forall m req, brk_r_ok m req (vm_brk (m_vmmaps m)) = true.
Proof.
intros m req. unfold brk_r_ok. cbv zeta. rewrite !bv_eqb_refl.
destruct (w_is0 req || _)%bool; [reflexivity|]. destruct (bv_unsigned req <? _)%Z; [apply orb_true_r|].
rewrite orb_true_r. cbn [andb]. unfold brk_grow_ok. cbv zeta. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.
#[export] Hint Resolve brk_r_ok_same : tot_witness.

Lemma brk_tot : forall req m0, TOT m0 (brk_spec req).
Proof. intros. tot_tac. Qed.
Lemma munmap_tot : forall a l m0, TOT m0 (munmap_spec a l).
Proof. intros. tot_tac. Qed.
Lemma mprotect_tot : forall a l p m0, TOT m0 (mprotect_spec a l p).
Proof. intros. tot_tac. Qed.
Lemma mmap_tot : forall a l p f fd off m0, TOT m0 (mmap_spec a l p f fd off).
Proof. intros. tot_tac. Qed.
