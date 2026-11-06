(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_unfold :=
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from, lowest_fd,
    set_fds, set_vmmaps, forget_vm_range,
    set_stdin, set_fs, set_halted, set_tid,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition out_det (eff : SyscallEffect) (m' : Model) (evs : list event)
    (o : outcome SyscallEffect) : Prop :=
  o = Ok eff m' evs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nodevnull (e : FdEntry) : FdEntry :=
  match e with FdUrandom => FdDir | _ => e end.

Lemma ioctl_tty_outcome : forall fd req i m e o,
  fd_lookup (m_fds m) fd = Some (nodevnull e) ->
  tty_only_request req = true ->
  ioctl_spec fd req i m o <->
  o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [].
Proof.
  intros fd req i m e0 o Hlk Hreq. set (e := nodevnull e0) in *.
  assert (ND : e <> FdUrandom) by (subst e; destruct e0; cbn; congruence).
  clearbody e. clear e0.
  unfold ioctl_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *;
      destruct e; try (exfalso; eapply ND; reflexivity); rewrite ?Hreq in *; inv_sys; reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. destruct e; try (exfalso; eapply ND; reflexivity); rewrite ?Hreq; reflexivity.
Qed.

(* [comment removed for export] *)

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

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
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
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hhas in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hhas.
    split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_err_out (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

Lemma mmap_err_out_enomem : forall m o,
  mmap_err_out m o <-> o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [].
Proof.
  intros m o. unfold mmap_err_out, mmap_errnos. split.
  - intros (e & [<- | []] & ->). reflexivity.
  - intros ->. exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
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
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Hanon, Hlen, Hmod. cbn [negb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. repeat split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _; (split; [reflexivity|]); (split; [|reflexivity]).
      eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noaccess_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
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
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Hanon, Hlen, Hmod, Hna. cbn [negb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. repeat split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _; (split; [reflexivity|]); (split; [|reflexivity]).
      eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
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
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
         (with_mmap_replacement flags addr n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
              ((addr, n) :: maps_subtract (vm_noaccess h)
                              (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h)
              (vm_init_sp h)) m)) []
  \/ (exists e, In e mmap_errnos
       /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                 (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfx. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. reflexivity.
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [-> | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_err_out (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

Lemma mprotect_err_out_enomem : forall m o,
  mprotect_err_out m o <-> o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [].
Proof.
  intros m o. unfold mprotect_err_out, mprotect_errnos. split.
  - intros (e & [<- | []] & ->). reflexivity.
  - intros ->. exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.

Lemma mprotect_expose_outcome : forall addr len prot i m o,
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
  mprotect_err_out m o
  \/ (mprotect_budget_ok m addr n = true
      /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) []).
Proof.
  intros addr len prot i m o Hgc Hal Hlen Hnw Hmod. cbv zeta. intros Hna Hma.
  unfold mprotect_spec.
  rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod. cbn [negb].
  unfold mprotect_err_out. sys_unfold.
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

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_reads (i : SyscallInput) (pathp : word) : list (word * nat) :=
  [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition open_res (m : Model) (mk : word -> Model) (o : outcome SyscallEffect) : Prop :=
  (exists e, In e openat_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
      /\ o = Ok (mkEffect (alloc_fd (m_fds m)) [] []) (mk (alloc_fd (m_fds m))) []).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma err_ret_outcome : forall e i m o,
  err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros. unfold err_ret, ret_only, pure. reflexivity. Qed.

Section Openat.
  Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
  Hypothesis Hfl : modeled_open_flags flags = true.

  (* [comment removed for export] *)
  Lemma openat_toolong_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrTooLong ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [].
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_empty_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk [] ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. cbn [path_eqb]. apply err_ret_outcome.
  Qed.

  Hypothesis Hdir : dirfd = AT_FDCWD32.
  Hypothesis Hrd : Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z.

  Lemma openat_body_resolved : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    openat_body_spec i m dirfd pathp flags i m o <-> openat_read_spec p m i m o.
  Proof.
    intros p o Hp Hne Hsl. unfold openat_body_spec. rewrite Hp.
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec. rewrite Hsl, Hrd.
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_absent_outcome : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    path_is_dirref p = false ->
    fs_lookup (m_fs m) p = None ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
  Proof.
    intros p o Hp Hne Hsl Hnd Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite Hnd, Hfs. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_dot_outcome : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> path_is_dirref p = true ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m) o.
  Proof.
    intros p o Hp Hdr. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    assert (Hne : p <> []).
    { intros ->. discriminate Hdr. }
    intros o'. rewrite (openat_body_resolved p o' Hp Hne (path_is_dirref_no_slash p Hdr)).
    unfold openat_read_spec. rewrite Hdr. apply open_result_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_file_outcome : forall p d o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    path_is_dirref p = false ->
    fs_lookup (m_fs m) p = Some d ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m
      (fun fd => with_fds (fd_insert (m_fds m) fd (FdFile p (Z_to_bv 64 0))) m) o.
  Proof.
    intros p d o Hp Hne Hsl Hnd Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite Hnd, Hfs. apply open_result_outcome.
  Qed.
End Openat.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma cap_iovecs_aux_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned, IH by lia. reflexivity.
Qed.

Lemma cap_iovecs_id_rw : forall iovs,
  (iovs_total iovs <= rw_bytes_max)%Z -> cap_iovecs iovs = iovs.
Proof.
  intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id.
  unfold MAX_RW_COUNT. unfold rw_bytes_max in H. lia.
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

(* [comment removed for export] *)
Lemma bind_input_get_model : forall (k : SyscallInput -> Model -> Sys SyscallEffect) i m o,
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

(* [comment removed for export] *)
Lemma writev_chan_outcome : forall fd iov iovcnt i m o ch iovs bs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  w_is0 ch = false ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (iovs_total iovs <= rw_bytes_max)%Z ->
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
  pose proof (cap_iovecs_id_rw iovs Htot) as Hcap.
  assert (Herrk : forall k, (k <= length bs)%nat ->
            addr_is_error_b (len_word (firstn k bs)) = false).
  { intros k Hk. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (rewrite firstn_length_le by lia; unfold two_pow_64;
                                   unfold rw_bytes_max in Htot; lia).
    rewrite firstn_length_le by lia. unfold rw_bytes_max in Htot. lia. }
  unfold writev_spec. rewrite bind_input_get_model. rewrite Hfd, Hch. cbv iota.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ds <- choose (fun ds : list byte =>
                       (1 <= Z.of_nat (length ds))%Z
                       /\ (Z.of_nat (length ds) < two_pow_64)%Z
                       /\ addr_is_error_b (len_word ds) = false
                       /\ ds = firstn (length ds) bs) ;;
        emit (map (WriteEv ch) ds) ;;
        record_copyins (iov_prefix_accesses (cap_iovecs iovs) (length ds))
          (ret_only (len_word ds)))%sys i m o).
  { rewrite Himp. cbv zeta. unfold writev_gathered.
    rewrite Hcap, (gather_prefix_full _ _ _ Hg).
    replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (addr_is_error_b (len_word bs)) with false
      by (symmetry; rewrite <- (firstn_all bs); rewrite (Herrk (length bs)) by lia; reflexivity).
    reflexivity. }
  rewrite Hcap. sys_unfold.
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
        rewrite Hlk. split; [lia|]. split; [unfold two_pow_64, rw_bytes_max in *; lia|].
        split; [apply Herrk; lia|reflexivity].
      * split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
        eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + rewrite Hlk, !app_nil_r. unfold len_word. rewrite Hlk. split; reflexivity.
Qed.

(* [comment removed for export] *)
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
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_rw; unfold rw_bytes_max; lia).
  unfold writev_spec. rewrite bind_input_get_model. rewrite Hfd, Hch. cbv iota.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ret_only (Z_to_bv 64 0)) i m o).
  { rewrite Himp. cbv zeta. rewrite Hcap, Htot. cbn [Z.eqb]. reflexivity. }
  rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.
